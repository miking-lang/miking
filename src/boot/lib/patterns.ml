open Utils
open Ast
open Ustring.Op
open Intrinsics
module UstringSet = Set.Make (Ustring)

(* This is taken from Core: https://github.com/monadbobo/ocaml-core/blob/9c1c06e7a1af7e15b6019a325d7dbdbd4cdb4020/base/core/lib/core_list.ml#L566-L571 *)
let concat_map l ~f =
  let rec aux acc = function
    | [] ->
        List.rev acc
    | hd :: tl ->
        aux (List.rev_append (f hd) acc) tl
  in
  aux [] l

let rec split_at n = function
  | x :: xs when n > 0 ->
      let pre, post = split_at (n - 1) xs in
      (x :: pre, post)
  | l ->
      ([], l)

let repeat (n : int) (v : 'a) : 'a list = List.init n (fun _ -> v)

(* TODO(vipa): make lists and records similar, put both constructors here, move what's in the negative pattern to edge pattern for sequences, add an exact record pattern *)
type simple_con =
  | IntCon of int
  | CharCon of int
  | BoolCon of bool
  | ConCon of ustring
  | RecCon
  | SeqCon

module SimpleConOrd = struct
  type t = simple_con

  (* NOTE(?,?): I can't just use the polymorphic compare in the standard library
   * since ustring has internal mutation that would be visible to it, but
   * shouldn't affect the result *)
  let con_idx = function
    | IntCon _ ->
        0
    | CharCon _ ->
        1
    | BoolCon _ ->
        2
    | ConCon _ ->
        3
    | RecCon ->
        4
    | SeqCon ->
        5

  let compare a b =
    match (a, b) with
    | IntCon a, IntCon b ->
        Int.compare a b
    | CharCon a, CharCon b ->
        Int.compare a b
    | BoolCon a, BoolCon b ->
        Bool.compare a b
    | ConCon a, ConCon b ->
        Ustring.compare a b
    | _ ->
        Int.compare (con_idx a) (con_idx b)
end

module ConSet = Set.Make (SimpleConOrd)

type snpat =
  | NPatInt of int
  | NPatChar of int
  | NPatBool of bool
  | NPatCon of ustring * npat
  | NPatRecord of
      npat Record.t * UstringSet.t (* The set is disallowed labels *)
  | NPatSeqTot of npat list
  | NPatSeqEdge of
      npat list * IntSet.t (* The set of disallowed lengths *) * npat list

and npat = SNPat of snpat | NPatNot of ConSet.t

(* The disallowed simple constructors *)

let wildpat = NPatNot ConSet.empty

let notpat_simple c = NPatNot (ConSet.singleton c)

let simple_con_of_simple_pat = function
  | NPatInt i ->
      IntCon i
  | NPatChar c ->
      CharCon c
  | NPatBool b ->
      BoolCon b
  | NPatCon (c, _) ->
      ConCon c
  | NPatRecord _ ->
      RecCon
  | NPatSeqTot _ | NPatSeqEdge _ ->
      SeqCon

module NPatOrd = struct
  type t = npat

  let snpat_idx = function
    | NPatInt _ ->
        0
    | NPatChar _ ->
        1
    | NPatBool _ ->
        2
    | NPatCon _ ->
        3
    | NPatRecord _ ->
        4
    | NPatSeqTot _ ->
        5
    | NPatSeqEdge _ ->
        6

  let npat_idx = function SNPat _ -> 0 | NPatNot _ -> 1

  let rec compare_list a b =
    match (a, b) with
    | [], [] ->
        0
    | x :: xs, y :: ys ->
        let pat_res = compare x y in
        if pat_res = 0 then compare_list xs ys else pat_res
    | [], _ :: _ ->
        -1
    | _ :: _, [] ->
        1

  and compare_snpat a b =
    match (a, b) with
    | NPatInt a, NPatInt b ->
        Int.compare a b
    | NPatChar a, NPatChar b ->
        Int.compare a b
    | NPatBool a, NPatBool b ->
        Bool.compare a b
    | NPatCon (str1, p1), NPatCon (str2, p2) ->
        let str_res = Ustring.compare str1 str2 in
        if str_res = 0 then compare p1 p2 else str_res
    | NPatRecord (a1, d1), NPatRecord (a2, d2) ->
        let rec_res = Record.compare compare a1 a2 in
        if rec_res = 0 then UstringSet.compare d1 d2 else rec_res
    | NPatSeqTot a, NPatSeqTot b ->
        compare_list a b
    | NPatSeqEdge (pre1, len1, post1), NPatSeqEdge (pre2, len2, post2) ->
        let pre_res = compare_list pre1 pre2 in
        if pre_res <> 0 then pre_res
        else
          let mid_res = IntSet.compare len1 len2 in
          if mid_res <> 0 then mid_res else compare_list post1 post2
    | _ ->
        Int.compare (snpat_idx a) (snpat_idx b)

  and compare a b =
    match (a, b) with
    | SNPat a, SNPat b ->
        compare_snpat a b
    | NPatNot cons1, NPatNot cons2 ->
        ConSet.compare cons1 cons2
    | _ ->
        Int.compare (npat_idx a) (npat_idx b)
end

module NPatSet = Set.Make (NPatOrd)

type normpat = NPatSet.t

let traverse (f : 'a -> 'b list) (l : 'a list) : 'b list list =
  let rec go = function
    | [] ->
        [[]]
    | x :: xs ->
        let tails = go xs in
        let heads = f x in
        concat_map tails ~f:(fun tl -> List.map (fun hd -> hd :: tl) heads)
  in
  go l

let sequence (l : 'a list list) : 'a list list =
  let rec go = function
    | [] ->
        [[]]
    | x :: xs ->
        let tails = go xs in
        let heads = x in
        concat_map tails ~f:(fun tl -> List.map (fun hd -> hd :: tl) heads)
  in
  go l

let liftA2 (f : 'a -> 'b -> 'c) (la : 'a list) (lb : 'b list) : 'c list =
  concat_map la ~f:(fun a -> List.map (f a) lb)

let map2_with_extras (f : 'a -> 'b -> 'c) (extra_a : 'a) (extra_b : 'b) :
    'a list -> 'b list -> 'c list =
  let rec recur la lb =
    match (la, lb) with
    | [], [] ->
        []
    | [], b :: lb ->
        f extra_a b :: recur [] lb
    | a :: la, [] ->
        f a extra_b :: recur la []
    | a :: la, b :: lb ->
        f a b :: recur la lb
  in
  recur

let map2_keep_extras (f : 'a -> 'a -> 'b) :
    'a list -> 'a list -> (bool * 'a list) option * 'b list =
  let rec recur la lb =
    match (la, lb) with
    | [], [] ->
        (None, [])
    | [], _ :: _ ->
        (Some (true, lb), [])
    | _ :: _, [] ->
        (Some (false, la), [])
    | a :: la, b :: lb ->
        let extras, res = recur la lb in
        (extras, f a b :: res)
  in
  recur

let include_tail (f : 'a -> 'b) : (bool * 'a list) option * 'b list -> 'b list
    = function
  | None, pre ->
      pre
  | Some (_, tail), pre ->
      pre @ List.map f tail

(* This function takes the complement of a product, i.e., it produces
   a pattern that matches if at least one of the subpatterns of the
   product does not match. *)
let rec list_complement (constr : npat list -> npat) (l : npat list) : normpat
    =
  let len = List.length l in
  (* NOTE(vipa, 2021-08-24): There are two versions here:

     - One that is O(2^n), but it produces disjoint patterns
     - One that is O(n^2), but the patterns overlap

     Later analyses, intersection in particular, end up being
     exponential in the number of unioned patterns, which means
     that overlapping patterns are problematic. The intersection
     of two overlapping patterns sticks around, the intersection
     of non-overlapping patterns do not, thus later stages get
     much larger inputs in some cases when we pick the O(n^2)
     version.

     At present we thus pick which algorithm to use based on
     the length of the given list, which appears to manage more
     cases than using either algorithm exclusively does. *)
  if len < 5 then
    traverse (fun p -> [NPatSet.singleton p; npat_complement p]) l
    (* Produce all combinations of (complement this) (don't complement this)
       for each element in the list. Length of this list is thus 2^(length l) *)
    |> List.tl (* Remove the list that doesn't complement anything *)
    (* We now have a normpat list list, where the inner list has length `length l`.
       We want to have a npat list list, where the outermost list will be turned into
       a normpat (after calling constr). We must thus move the multiplicity present in
       normpat (since it's a set) up to the top-most list, which we can do using `traverse`
       in the list monad. *)
    |> concat_map ~f:(fun np_list ->
           traverse NPatSet.elements np_list |> List.map constr )
    |> NPatSet.of_list
  else
    (* NOTE(vipa, 2021-08-18):
       This works by creating a digagonal of complemented patterns, e.g.,
       given input `[a, b, c]` we compute something like this:
         [!a, _, _]
       | [_, !b, _]
       | [_, _, !c]
    *)
    List.init len (fun target ->
        let f i p =
          if i = target then NPatSet.elements (npat_complement p) else [wildpat]
        in
        List.mapi f l )
    (* NOTE(vipa, 2021-08-18): `npat_complement` produces a normpat, which
       we here treat as a list of patterns that are unioned together. This
       means that we presently have something like this:
         [(a1 | a2 | ...), _, _]
       | [_, (b1 | b2 | ...), _]
       | [_, _, (c1 | c2 | ...)]
       Note that a sequence of unions is represented by a list here, so
       this is a list of lists of lists of npats. For a single list
       (e.g., `[(a1 | a2 | ...), _, _]`) this means we can move the
       unions to the top-level using `sequence` in the list monad, at which
       point the only thing we need to do is concat the results, which
       we can do in one step with `concat_map`. *)
    |> concat_map ~f:sequence
    (* NOTE(vipa, 2021-08-18): Finally, we apply `constr` to take each
       `npat list` and make it into an `npat`, which become the components
       of the final normpat. *)
    |> List.map constr
    |> NPatSet.of_list

(* construct a normpat *)
and npat_complement : npat -> normpat = function
  | SNPat (NPatInt i) ->
      notpat_simple (IntCon i) |> NPatSet.singleton
  | SNPat (NPatChar c) ->
      notpat_simple (CharCon c) |> NPatSet.singleton
  | SNPat (NPatBool b) ->
      notpat_simple (BoolCon b) |> NPatSet.singleton
  | SNPat (NPatCon (c, p)) ->
      npat_complement p
      |> NPatSet.map (fun p -> SNPat (NPatCon (c, p)))
      |> NPatSet.add (notpat_simple (ConCon c))
  | SNPat (NPatRecord (pats, neg_labels)) ->
      let with_forbidden_labels =
        UstringSet.elements neg_labels
        |> List.map (fun label ->
               SNPat
                 (NPatRecord (Record.add label wildpat pats, UstringSet.empty)) )
        |> NPatSet.of_list
      in
      let labels, pats = Record.bindings pats |> List.split in
      let complemented_product =
        list_complement
          (fun pats ->
            List.combine labels pats |> List.to_seq |> Record.of_seq
            |> fun x -> SNPat (NPatRecord (x, UstringSet.empty)) )
          pats
      in
      let missing_labels =
        labels
        |> List.map (fun label ->
               SNPat (NPatRecord (Record.empty, UstringSet.singleton label)) )
        |> NPatSet.of_list
      in
      NPatSet.union complemented_product missing_labels
      |> NPatSet.union with_forbidden_labels
  | SNPat (NPatSeqTot pats) ->
      list_complement (fun pats -> SNPat (NPatSeqTot pats)) pats
      |> NPatSet.add
           (SNPat (NPatSeqEdge ([], List.length pats |> IntSet.singleton, [])))
  | SNPat (NPatSeqEdge (pre, lens, post)) ->
      let lenPre, lenPost = (List.length pre, List.length post) in
      let complemented_product =
        list_complement
          (fun pats ->
            let pre, post = split_at lenPre pats in
            SNPat (NPatSeqEdge (pre, lens, post)) )
          (pre @ post)
      in
      let allowed_lengths =
        List.init (lenPre + lenPost) (fun n ->
            if IntSet.mem n lens then None
            else Some (SNPat (NPatSeqTot (repeat n wildpat))) )
        |> List.filter_map (fun x -> x)
        |> NPatSet.of_list
      in
      NPatSet.union complemented_product allowed_lengths
      |> NPatSet.add (notpat_simple SeqCon)
  | NPatNot cons ->
      ConSet.elements cons
      |> List.map (function
           | IntCon i ->
               SNPat (NPatInt i)
           | CharCon c ->
               SNPat (NPatChar c)
           | BoolCon b ->
               SNPat (NPatBool b)
           | ConCon c ->
               SNPat (NPatCon (c, wildpat))
           | SeqCon ->
               SNPat (NPatSeqEdge ([], IntSet.empty, []))
           | RecCon ->
               SNPat (NPatRecord (Record.empty, UstringSet.empty)) )
      |> NPatSet.of_list

and npat_intersect (a : npat) (b : npat) : normpat =
  match (a, b) with
  | NPatNot cons1, NPatNot cons2 ->
      NPatSet.singleton (NPatNot (ConSet.union cons1 cons2))
  | NPatNot cons, (SNPat sp as pat) | (SNPat sp as pat), NPatNot cons ->
      if ConSet.mem (simple_con_of_simple_pat sp) cons then NPatSet.empty
      else NPatSet.singleton pat
  | SNPat p1, SNPat p2 -> (
    match (p1, p2) with
    | NPatInt i1, NPatInt i2 when i1 = i2 ->
        NPatSet.singleton a
    | NPatChar c1, NPatChar c2 when c1 = c2 ->
        NPatSet.singleton a
    | NPatBool b1, NPatBool b2 when b1 = b2 ->
        NPatSet.singleton a
    | NPatCon (s1, p1), NPatCon (s2, p2) when s1 = s2 ->
        npat_intersect p1 p2 |> NPatSet.map (fun p -> SNPat (NPatCon (s1, p)))
    | NPatRecord (r1, neg1), NPatRecord (r2, neg2) ->
        if
          Record.exists (fun label _ -> UstringSet.mem label neg2) r1
          || Record.exists (fun label _ -> UstringSet.mem label neg1) r2
        then NPatSet.empty
        else
          let neg = UstringSet.union neg1 neg2 in
          let merge_f _ a b =
            match (a, b) with
            | None, None ->
                None
            | Some a, Some b ->
                Some (npat_intersect a b |> NPatSet.elements)
            | Some a, _ | _, Some a ->
                Some [a]
          in
          Record.merge merge_f r1 r2 |> Record.bindings
          |> traverse (fun (k, vs) -> List.map (fun v -> (k, v)) vs)
          |> List.map (fun bindings ->
                 SNPat (NPatRecord (List.to_seq bindings |> Record.of_seq, neg)) )
          |> NPatSet.of_list
    | NPatSeqTot pats1, NPatSeqTot pats2 ->
        if List.length pats1 <> List.length pats2 then NPatSet.empty
        else
          List.map2 npat_intersect pats1 pats2
          |> traverse NPatSet.elements
          |> List.map (fun pats -> SNPat (NPatSeqTot pats))
          |> NPatSet.of_list
    | NPatSeqEdge (pre1, lens1, post1), NPatSeqEdge (pre2, lens2, post2) ->
        let lens = IntSet.union lens1 lens2 in
        let pre = map2_keep_extras npat_intersect pre1 pre2 in
        let rev_post =
          map2_keep_extras npat_intersect (List.rev post1) (List.rev post2)
        in
        let simple =
          let pre = include_tail NPatSet.singleton pre in
          let post = List.rev (include_tail NPatSet.singleton rev_post) in
          pre @ post |> traverse NPatSet.elements
          |> List.map (fun pats ->
                 let pre, post = split_at (List.length pre) pats in
                 SNPat (NPatSeqEdge (pre, lens, post)) )
          |> NPatSet.of_list
        in
        (* NOTE(vipa, 2021-08-23): We need to consider when the
           opposite ends of the two patterns overlap, e.g.,
           `([1] ++ _) & (_ ++ [1])` should match the list `[1]`,
           i.e., `[1] ++ _ ++ [1]` is not enough. *)
        let overlapping =
          match (pre, rev_post) with
          | ( (Some (pre_dir, pre_extras), pre)
            , (Some (post_dir, rev_post_extras), rev_post) )
            when pre_dir <> post_dir ->
              let post = List.rev rev_post in
              let post_extras = List.rev rev_post_extras in
              List.init (List.length pre_extras) (fun n ->
                  List.rev_append (repeat n wildpat) post_extras
                  |> map2_with_extras npat_intersect wildpat wildpat pre_extras
                  |> fun mid -> pre @ mid @ post )
              |> concat_map ~f:(traverse NPatSet.elements)
              |> List.map (fun pats -> SNPat (NPatSeqTot pats))
              |> NPatSet.of_list
          | _ ->
              NPatSet.empty
        in
        NPatSet.union simple overlapping
    | NPatSeqEdge (pre, lens, post), NPatSeqTot pats
    | NPatSeqTot pats, NPatSeqEdge (pre, lens, post) ->
        let len_pre, len_post, len_pats =
          (List.length pre, List.length post, List.length pats)
        in
        if IntSet.mem len_pats lens then NPatSet.empty
        else if len_pre + len_post > len_pats then NPatSet.empty
        else
          pre @ repeat (len_pats - len_pre - len_post) wildpat @ post
          |> List.map2 npat_intersect pats
          |> traverse NPatSet.elements
          |> List.map (fun pats -> SNPat (NPatSeqTot pats))
          |> NPatSet.of_list
    | _ ->
        if
          SimpleConOrd.compare
            (simple_con_of_simple_pat p1)
            (simple_con_of_simple_pat p2)
          <> 0
        then NPatSet.empty
        else Msg.raise_error NoInfo "Impossible" )

and normpat_complement (np : normpat) : normpat =
  NPatSet.elements np |> List.map npat_complement
  |> List.fold_left normpat_intersect (NPatSet.singleton wildpat)

and normpat_intersect (a : normpat) (b : normpat) : normpat =
  liftA2 npat_intersect (NPatSet.elements a) (NPatSet.elements b)
  |> List.fold_left NPatSet.union NPatSet.empty

let normpat_subset (a : normpat) (b : normpat) : bool =
  normpat_intersect a (normpat_complement b) |> NPatSet.is_empty

let normpat_overlap (a : normpat) (b : normpat) : bool =
  (* This is a shortcut optimization on normpat_intersect a b |> NPatSet.is_empty |> not,
   * lessening the minimum number of calls to npat_intersect. *)
  liftA2 (fun a b -> (a, b)) (NPatSet.elements a) (NPatSet.elements b)
  |> List.exists (fun (a, b) -> npat_intersect a b |> NPatSet.is_empty |> not)

let rec pat_to_normpat = function
  | PatNamed _ ->
      NPatSet.singleton wildpat
  | PatSeqTot (_, pats) ->
      Mseq.Helpers.to_list pats
      |> traverse (fun p -> pat_to_normpat p |> NPatSet.elements)
      |> List.map (fun pats -> SNPat (NPatSeqTot pats))
      |> NPatSet.of_list
  | PatSeqEdge (_, pre, _, post) ->
      Mseq.concat pre post |> Mseq.Helpers.to_list
      |> traverse (fun p -> pat_to_normpat p |> NPatSet.elements)
      |> List.map (fun pats ->
             let pre, post = split_at (Mseq.length pre) pats in
             SNPat (NPatSeqEdge (pre, IntSet.empty, post)) )
      |> NPatSet.of_list
  | PatRecord (_, r) ->
      Record.bindings r
      |> traverse (fun (k, p) ->
             pat_to_normpat p |> NPatSet.elements |> List.map (fun p -> (k, p)) )
      |> List.map (fun bindings ->
             SNPat
               (NPatRecord
                  (List.to_seq bindings |> Record.of_seq, UstringSet.empty) ) )
      |> NPatSet.of_list
  | PatCon (_, c, _, p) ->
      pat_to_normpat p |> NPatSet.map (fun p -> SNPat (NPatCon (c, p)))
  | PatInt (_, i) ->
      NPatSet.singleton (SNPat (NPatInt i))
  | PatChar (_, c) ->
      NPatSet.singleton (SNPat (NPatChar c))
  | PatBool (_, b) ->
      NPatSet.singleton (SNPat (NPatBool b))
  | PatAnd (_, a, b) ->
      normpat_intersect (pat_to_normpat a) (pat_to_normpat b)
  | PatOr (_, a, b) ->
      NPatSet.union (pat_to_normpat a) (pat_to_normpat b)
  | PatNot (_, p) ->
      normpat_complement (pat_to_normpat p)

let pat_example_gives_complete_pattern = ref false

let pat_example normpat =
  let wildpat = PatNamed (NoInfo, NameWildcard) in
  let rec npat_to_pat = function
    | SNPat (NPatInt i) ->
        PatInt (NoInfo, i)
    | SNPat (NPatChar c) ->
        PatChar (NoInfo, c)
    | SNPat (NPatBool b) ->
        PatBool (NoInfo, b)
    | SNPat (NPatCon (str, np)) ->
        PatCon (NoInfo, str, Symb.Helpers.nosym, npat_to_pat np)
    | SNPat (NPatRecord (r, neg)) -> (
        let pos = PatRecord (NoInfo, Record.map npat_to_pat r) in
        UstringSet.elements neg
        |> List.map (fun label ->
               PatRecord (NoInfo, Record.singleton label wildpat) )
        |> function
        | [] ->
            pos
        | x :: xs ->
            let neg =
              PatNot
                (NoInfo, List.fold_left (fun a b -> PatOr (NoInfo, a, b)) x xs)
            in
            if Record.is_empty r then neg else PatAnd (NoInfo, pos, neg) )
    | SNPat (NPatSeqTot nps) ->
        PatSeqTot (NoInfo, List.map npat_to_pat nps |> Mseq.Helpers.of_list)
    | SNPat (NPatSeqEdge (pre, lens, post)) ->
        let rem_len acc len =
          PatAnd
            ( NoInfo
            , acc
            , PatSeqTot (NoInfo, repeat len wildpat |> Mseq.Helpers.of_list) )
        in
        let base =
          PatSeqEdge
            ( NoInfo
            , List.map npat_to_pat pre |> Mseq.Helpers.of_list
            , NameWildcard
            , List.map npat_to_pat post |> Mseq.Helpers.of_list )
        in
        List.fold_left rem_len base (IntSet.elements lens)
    | NPatNot cons -> (
        let cons =
          ConSet.elements cons
          |> List.map (function
               | IntCon i ->
                   PatInt (NoInfo, i)
               | CharCon c ->
                   PatChar (NoInfo, c)
               | BoolCon b ->
                   PatBool (NoInfo, b)
               | ConCon str ->
                   PatCon (NoInfo, str, Symb.Helpers.nosym, wildpat)
               | SeqCon ->
                   PatSeqEdge (NoInfo, Mseq.empty, NameWildcard, Mseq.empty)
               | RecCon ->
                   PatRecord (NoInfo, Record.empty) )
        in
        match cons with
        | [] ->
            wildpat
        | p :: ps ->
            PatNot
              (NoInfo, List.fold_left (fun a b -> PatOr (NoInfo, a, b)) p ps) )
  in
  if !pat_example_gives_complete_pattern then
    match NPatSet.elements normpat with
    | [] ->
        PatNot (NoInfo, PatNamed (NoInfo, NameWildcard))
    | np :: nps ->
        List.fold_left
          (fun a b -> PatOr (NoInfo, a, npat_to_pat b))
          (npat_to_pat np) nps
  else
    match NPatSet.choose_opt normpat with
    | None ->
        PatNot (NoInfo, PatNamed (NoInfo, NameWildcard))
    | Some np ->
        npat_to_pat np

type order_query =
  | Subset
  | Superset
  | Equal
  | Disjoint
  | Overlapping of pat * pat * pat

(* examples of patterns in only left, in both, and in only right *)

(* Compare the specificity order of two patterns. If you want to compare two patterns p1 and p2,
 * pass the arguments (pat_to_normpat p1, normpat_complement (pat_to_normpat p1)) and
 * (pat_to_normpat p2, normpat_complement (pat_to_normpat p2)). *)
let order_query ((ap, an) : normpat * normpat) ((bp, bn) : normpat * normpat) :
    order_query =
  let a_minus_b = normpat_intersect ap bn in
  let b_minus_a = normpat_intersect bp an in
  if NPatSet.is_empty a_minus_b && NPatSet.is_empty b_minus_a then Equal
  else if NPatSet.is_empty a_minus_b then Subset
  else if NPatSet.is_empty b_minus_a then Superset
  else
    let overlapping = normpat_intersect ap bp in
    if NPatSet.is_empty overlapping then Disjoint
    else
      Overlapping
        (pat_example a_minus_b, pat_example overlapping, pat_example b_minus_a)
