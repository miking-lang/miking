include "seq.mc"
include "string.mc"

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
    | BFloat {instr: String, nr: Float}
    | BLong {instr: String, nr: Int}

    syn Field =
    | Field {name: String, t: String}

    syn Function = 
    | Function {name: String, descriptor: String, bytecode: [Bytecode]}

    syn Class =
    | Class {implements: String, name: String, fields: [Field], constructor: Function, functions: [Function]}

    syn Interface =
    | Interface {name: String, fields: [Field], functions: [Function]}

    syn JVMProgram = 
    | JVMProgram {package: String, classes: [Class], interfaces: [Interface]}

    ----
    sem getNameField : Field -> String
    sem getNameField =
    | Field {name = name} -> name

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

    sem createBFloat : String -> Float -> Bytecode
    sem createBFloat instr =
    | nr -> BFloat {instr = instr, nr = nr}

    sem createBLong : String -> Int -> Bytecode
    sem createBLong instr =
    | nr -> BLong {instr = instr, nr = nr}

    sem createFunction : String -> String -> [Bytecode] -> Function
    sem createFunction name descriptor =
    | bytecode -> Function {name = name, descriptor = descriptor, bytecode = bytecode}

    sem createProg : String -> [Class] -> [Interface] -> JVMProgram
    sem createProg package classes =
    | interfaces -> JVMProgram {package = package, classes = classes, interfaces = interfaces}

    sem createClass : String -> String -> [Field] -> Function -> [Function] -> Class
    sem createClass name implements fields constructor =
    | functions -> Class {name = name, implements = implements, fields = fields, constructor = constructor, functions = functions}

    sem createInterface : String -> [Field] -> [Function] -> Interface
    sem createInterface name fields =
    | functions -> Interface {name = name, fields = fields, functions = functions}

    sem createField : String -> String -> Field
    sem createField name =
    | t -> Field {name = name, t = t} 

    -- toString JSON

    sem toStringProg : JVMProgram -> String 
    sem toStringProg = 
    | JVMProgram {package = package, classes = classes, interfaces = interfaces} -> 
        (join["{", "\"package\":", (stringify package), ",\"interfaces\":[", (commaSeparate (map toStringInterface interfaces)), "],\"classes\":[", (commaSeparate (map toStringClass classes)), "]}"])

    sem toStringClass : Class -> String
    sem toStringClass =
    | Class {name = n, implements = implements, fields = f, constructor = c, functions = fun} ->
        (join ["{", "\"implements\":", (stringify implements), ",\"name\":", (stringify n), ",\"fields\":[", (commaSeparate (map toStringField f)), "],\"constructor\":", (toStringFunction c), ",\"functions\":[", (commaSeparate (map toStringFunction fun)), "]}"])

    sem toStringInterface : Interface -> String
    sem toStringInterface =
    | Interface {name = n, fields = f, functions = fun} ->
        (join ["{", "\"name\":", (stringify n), ",\"fields\":[", (commaSeparate (map toStringField f)), "],\"functions\":[", (commaSeparate (map toStringFunction fun)), "]}"])

    sem toStringField : Field -> String
    sem toStringField =
    | Field {name = name,  t = t} ->
        (join ["{", "\"name\":", (stringify name), ",\"type\":", (stringify t), "}"])

    sem toStringFunction : Function -> String
    sem toStringFunction =
    | Function {name = n, descriptor = d, bytecode = b} ->
        (join ["{", "\"name\":", (stringify n), ",\"descriptor\":", (stringify d), ",\"bytecode\":[", (commaSeparate (map toStringBytecode b)), "]}"])

    sem toStringBytecode : Bytecode -> String
    sem toStringBytecode =
    | BApply {instr = i, owner = o, name = n, descriptor = d} ->
        (join ["{", "\"type\":", "\"apply\"", ",\"instr\":", (stringify i), ",\"owner\":", (stringify o), ",\"name\":", (stringify n), ",\"descriptor\":", (stringify d), "}"])
    | BString {instr = i, constant = c} ->
        (join ["{", "\"type\":", "\"arg_constant\"", ",\"instr\":", (stringify i), ",\"constant\":", (stringify c), "}"])
    | BInt {instr = i, nr = nr } ->
        (join ["{", "\"type\":", "\"arg_int\"", ",\"instr\":", (stringify i), ",\"nr\":", (int2string nr), "}"])
    | BFloat {instr = i, nr = nr } ->
        (join ["{", "\"type\":", "\"arg_float\"", ",\"instr\":", (stringify i), ",\"nr\":", (concat (float2string nr) "0"), "}"])
    | BLong {instr = i, nr = nr } ->
        (join ["{", "\"type\":", "\"arg_long\"", ",\"instr\":", (stringify i), ",\"nr\":", (int2string nr), "}"])
    | BEmpty {instr = i} ->
        (join ["{", "\"type\":", "\"empty\"", ",\"instr\":", (stringify i), "}"])

end