
include "data-frame.mc"
include "search-space.mc"
include "instrumentation.mc"
include "math.mc"

include "mexpr/cmp.mc"

lang Database = MExprEq + MExprCmp + Instrumentation
  syn Database =
  | Database {
      -- The 'i'th row of 'tables' gives the table used in the 'i'th iteration.
      tables : DataFrame Expr,
      -- The 'i'th row of 'runs' gives the count of how many times a measuring
      -- point was run in the 'i'th iteration. The 'j'th element of each row
      -- considers the measuring point with id 'j + offset', with 'offset' from
      -- the dependency graph.
      runs : DataFrame Int,
      -- Like 'runs', but stores the total time spent (in ms) in a measuring
      -- point.
      totals : DataFrame Float
    }

  -- 'databaseEmpty n m' returns a new database designed for 'n' holes and 'm'
  -- measuring points.
  sem databaseEmpty (nbrHoles : Int) =
  | nbrMeas ->
    Database {
      tables = dataFrameFromSeq [] nbrHoles,
      runs = dataFrameFromSeq [] nbrMeas,
      totals = dataFrameFromSeq [] nbrMeas
    }

  -- 'databaseAddRun str db' reads the profiled result 'str' from a program run and
  -- stores it in 'db'.
  sem databaseAddRun (table: [Expr]) (profile: InstrumentationProfile)
                     (offset: Int) =
  | Database db ->
    match profile with
      {ids= ids, nbrRuns= nbrRuns, totalMs= totalMs} in
    -- Assert: dimensions match
    utest length ids with db.runs.ncols using eqi in
    utest length nbrRuns with db.runs.ncols using eqi in
    utest length totalMs with db.runs.ncols using eqi in
    -- Assert: the 'ids' are stored contiguously as offset..(offset+nbrMeas-1)
    utest ids with create db.runs.ncols (lam i. addi offset i)
    using eqSeq eqi in

    Database { { { db with runs = dataFrameAddRow nbrRuns db.runs }
                      with totals = dataFrameAddRow totalMs db.totals }
                      with tables = dataFrameAddRow table db.tables }

  -- 'databaseCost i dep' returns the estimated total execution time in ms of
  -- the 'i'th entry stored in 'db'.
  sem databaseCost (i : Int) =
  | Database db ->
    let row = dataFrameGetRow i db.totals in
    foldl addf 0. row

  -- 'databaseCostSlice i idxs dep' returns the estimated total execution time
  -- in ms of the 'i'th entry stored in 'db', with measuring point indices
  -- 'idxs' sliced out.
  sem databaseCostSlice (i : Int) (idxs : [Int]) =
  | Database db ->
    let row = dataFrameGetRowSlice i idxs db.totals in
    foldl addf 0. row

  -- 'databaseOptimal epsilon ss db' returns the most optimal table and its
  -- estimated execution time, given the result in 'db' and taking into account
  -- the dependencies in 'dep'.
  sem databaseOptimal (epsilon : Float) (dep : DependencyGraph)
                      (ss : SearchSpaceSize) =
  | Database db ->
    -- Find connected components
    let ccs : [[Int]] = map (lam c: ([Int], Float). c.0) ss.connectedComponents in
    -- Partition into holes and measuring points, and offset measuring points
    -- (to use as indices into database)
    let ccs : [([Int],[Int])] = map (lam cc: [Int].
        let p = partition (lam v. lti v dep.offset) cc in
        (p.0, map (lam m. subi m dep.offset) p.1)
      ) ccs in
    -- For each connected component, choose the table minimizing the total
    -- execution time, add to the table
    match foldl (lam acc : (DataFrame (Option Expr), Float). lam hm : ([Int],[Int]).
      match hm with (hIdxs, mIdxs) in
      match databaseOptimalH epsilon hIdxs mIdxs dep (Database db) with
        (minCost, slice)
      in
        ( dataFrameSetRowSlice 0 hIdxs (map (lam v. Some v) slice) acc.0,
          addf acc.1 minCost )
      ) (dataFrameFromSeq [make db.tables.ncols (None ())] db.tables.ncols, 0.) ccs
    with (minDF, minMs) in
    -- Convert the data frame to a lookup table
    let minOpt: [Option Expr] = dataFrameGetRow 0 minDF in
    let table: [Expr] = mapi (lam i. lam o.
        match o with Some v then v
        -- If a hole was not assigned a value, it means it does not affect a
        -- measuring point. Use its first recorded value in the data base.
        else
          get (dataFrameGetRow 0 db.tables) i
      ) minOpt in
    (table, minMs)

    sem databaseOptimalH (epsilon : Float) (hIdxs : [Int]) (mIdxs : [Int])
                         (dep : DependencyGraph) =
    | Database db ->
      -- Assert that indices are monotonically increasing (or indexing breaks)
      utest eqSeq eqi hIdxs (sort subi hIdxs) with true in
      -- Pick out the domains from the database
      let tables = dataFrameSlice hIdxs db.tables in
      let totals = dataFrameSlice mIdxs db.totals in
      let domains : Map Int (Set Expr) = foldl (lam acc. lam h.
          mapInsert h (setEmpty cmpExpr) acc
        ) (mapEmpty subi) hIdxs
      in
      let domains : Map Int (Set Expr) = foldl (lam acc. lam row.
          foldl (lam acc. lam hVal.
              match hVal with (h, val) in
              let old = mapFindExn h acc in
              let new = setInsert val old in
              mapInsert h new acc
            ) acc (zip hIdxs row)
        ) domains tables
      in

      let tupleCost : [Expr] -> Option Float = lam tuple.
        -- Check whether the tuple is valid for each measuring point, add the
        -- cost if it is.
        foldl (lam acc: Option Float. lam m: Int.
          match acc with Some someAcc then
            let hs = graphNeighbors (addi m dep.offset) dep.graph in
            -- Assert that indices are monotonically increasing (or indexing breaks)
            utest eqSeq eqi hs (sort subi hs) with true in
            let idxs = map (lam h.
                match index (eqi h) hIdxs with Some i then i
                else error "impossible"
              ) hs
            in
            let tupleSlice = map (lam i. get tuple i) idxs in
            match dataFrameHasRowSlice eqExpr hs tupleSlice db.tables
            with Some row
            then Some (addf someAcc (head (dataFrameGetRowSlice row [m] db.totals)))
            else None ()
          else None ()
        ) (Some 0.) mIdxs
      in

      let domainSeqs : [[Expr]] = map setToSeq (mapValues domains) in

      let tuples = searchSpaceProduct domainSeqs in
      let costs : [Option Float] = map tupleCost tuples in
      let someCosts : [(Float, [Expr])] = foldl (lam acc. lam costTuple.
          match costTuple with (c, tuple) in
          match c with Some c then snoc acc (c, tuple)
          else acc
        ) [] (zip costs tuples)
      in
      match
        min (lam c1: (Float, [Expr]). lam c2: (Float, [Expr]).
            cmpfApprox epsilon c1.0 c2.0
          ) someCosts
      with Some costTuple then costTuple
      else error "Impossible: no valid configuration"

    -- 'databaseCount db' returns the number of entries stored in the database.
    sem databaseCount =
    | Database db ->
      dataFrameLength db.tables

    -- 'databaseGetTable i db' returns the 'i'th table stored in the database.
    sem databaseGetTable (i : Int) =
    | Database db ->
      dataFrameGetRow i (db.tables)

    -- 'databaseHasTableSlice idxs row db' returns true if the tables contains
    -- the slice specified by 'idxs' and 'row', otherwise false.
    sem databaseHasTableSlice (idxs : [Int]) (row : [Expr]) =
    | Database db ->
      use MExprEq in
      optionIsSome (dataFrameHasRowSlice eqExpr idxs row db.tables)
  end

mexpr

()
