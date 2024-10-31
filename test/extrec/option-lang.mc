lang OptionLang 
  syn Option = 
  | None {}
  | Some {val : Int}

  sem myMap f = 
  | None _ -> None {NoneType of nothing}
  | Some s -> 
    let val = f s.val in 
    Some {val = val}

  sem forceGet = 
  | Some s -> s.val
end

mexpr
use OptionLang in 
let incr = addi 1 in 
let x = Some {val = 10} in 

utest forceGet x with 10 in 

-- let s = match myMap incr x with Some s then s
--         else error "this can not happen!" in 
-- utest s.val with 11 in 
()