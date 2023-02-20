include "seq.mc"

--helper functions

recursive
    let commaSeparateHelper = lam seq. lam res.
        if eqi 0 (length seq) then 
            res
        else if eqi 1 (length seq) then
            join [res, ",", get seq 0]
        else commaSeparateHelper (tail seq) (join [res, ",", head seq])
end

let commaSeparate = lam seq.
    if eqi 0 (length seq) then 
        ""
    else commaSeparateHelper (tail seq) (head seq)

-- TODO: make sure to escape
let stringify = lam string.
    (join ["\"",  string, "\""])

lang JVMAst

    syn Bytecode = 
    | BString {instr: String, constant: String}
    | BApply {instr: String, owner: String, name: String, descriptor: String}
    | BEmpty {instr: String}
    | BInt {instr: String, nr: Int}

    syn Field =
    | Field {name: String, t: String}

    syn Function = 
    | Function {name: String, descriptor: String, bytecode: [Bytecode]}

    syn Class =
    | Class {name: String, fields: [Field], constructor: Function, functions: [Function]}

    syn Prog = 
    | Prog {classes: [Class]}

    type JVMEnv = {
        bytecode : [Bytecode]}

    -- create constructs

    sem createBString : String -> String -> Bytecode
    sem createBString instr = 
    | const -> BString {instr = instr, constant = const}

    sem createBApply : String -> String -> String -> String -> Bytecode
    sem createBApply instr owner name  =
    | descriptor -> BApply {instr = instr, name = name, owner = owner, descriptor = descriptor}

    sem createBEmpty : String -> Bytecode
    sem createBEmpty =
    | instr -> BEmpty {instr = instr}

    sem createBInt : String -> Int -> Bytecode
    sem createBInt instr =
    | nr -> BInt {instr = instr, nr = nr}

    sem createFunction : String -> String -> [Bytecode] -> Function
    sem createFunction name descriptor =
    | bytecode -> Function {name = name, descriptor = descriptor, bytecode = bytecode}

    sem createProg : [Class] -> Prog
    sem createProg =
    | classes -> Prog {classes = classes}

    sem createClass : String -> [Field] -> Function -> [Function] -> Class
    sem createClass name fields constructor =
    | functions -> Class {name = name, fields = fields, constructor = constructor, functions = functions}

    sem createField : String -> String -> Field
    sem createField name =
    | t -> Field {name = name, t = t} 

    -- toString JSON

    sem toStringProg : Prog -> String 
    sem toStringProg = 
    | Prog {classes = classes} -> (join ["{\"classes\":[", (commaSeparate (map toStringClass classes)), "]}"])

    sem toStringClass : Class -> String
    sem toStringClass =
    | Class {name = n, fields = f, constructor = c, functions = fun} ->
        (join ["{", "\"name\":", (stringify n), ",\"fields\":[", (commaSeparate (map toStringField f)), "],\"constructor\":", (toStringFunction c), ",\"functions\":[", (commaSeparate (map toStringFunction fun)), "]}"])

    sem toStringField : Field -> String
    sem toStringField =
    | Field {name = name,  t = t} ->
        (join ["{", "\"name\":", (stringify name), ",\"type\":", t, "}"])

    sem toStringFunction : Function -> String
    sem toStringFunction =
    | Function {name = n, descriptor = d, bytecode = b} ->
        (join ["{", "\"name\":", (stringify n), ",\"descriptor\":", (stringify d), ",\"bytecode\":[", (commaSeparate (map toStringBytecode b)), "]}"])

    sem toStringBytecode : Bytecode -> String
    sem toStringBytecode =
    | BApply {instr = i, owner = o, name = n, descriptor = d} ->
        (join ["{\"instr\":", (stringify i), ",\"owner\":", (stringify o), ",\"name\":", (stringify n), ",\"descriptor\":", (stringify d), "}"])
    | BString {instr = i, constant = c} ->
        (join ["{\"instr\":", (stringify i), ",\"constant\":", (stringify c), "}"])
    | BInt {instr = i, nr = nr } ->
        (join ["{", "\"instr\":", (stringify i), ",\"nr\":", (int2string nr), "}"])
    | BEmpty {instr = i} ->
        (join ["{\"instr\":", (stringify i), "}"])

end