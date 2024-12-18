lang OptionLang 
  syn Option a = 
  | None {}
  | Some {val : a}

  sem myMap f = 
  | None _ -> None {}
  | Some s -> Some {val = f s.val}

  sem forceGet = 
  | Some s -> s.val
end

mexpr
use OptionLang in 
let incr = addi 1 in 
let x = Some {val = 10} in 

print "\n";
print "\n";
utest forceGet x with 10 using eqi in 

let s = match myMap incr x with Some s then s
        else error "this can not happen!" in 
utest s.val with 11 using eqi in 
()