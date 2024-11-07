-- Rename head to v1 in this example please!
lang SomeLang 
  syn MyList = 
  | TmNil {}
  | TmCons {v1 : Int, v2 : Int, tail : MyList}

  sem addFirstTwo = 
  | TmCons {v1 = x, 
            tail = TmCons {v1 = y, tail = _}} -> addi x y
  | _ -> error "The list does not have at least two elements!"
end

mexpr
use SomeLang in
utest addFirstTwo (TmCons {v2 = 1, tail = TmCons {v2 = 2, tail = TmNil {}}}) with 3 using eqi in
()