lang OptionLang 
  syn Option a = 
  | None {}
  | Some {val : a}

  sem myMap f = 
  | None _ -> None {}
  | Some s -> Some {val = f s.val}
end

mexpr
use OptionLang in 
let incr = addi 1 in 
let x = Some {val = 10} in 

let s = match myMap incr x with Some s then s
        else error "this can not happen!" in 
utest s.val with 11 in 
()