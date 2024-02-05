include "wasm-ast.mc"
include "string.mc"
include "seq.mc"
include "common.mc"

let indent2str = lam indent. make (muli indent 4) ' '
let indent2strnewline = lam indent. concat "\n" (make (muli indent 4) ' ')

lang WasmPPrint = WasmAST
    sem pprintInstr: Int -> Instr -> String
    sem pprintInstr indent = 
    | I32Const i -> join [indent2str indent, "(i32.const ", (int2string i), ")"]
    | LocalGet id -> join [indent2str indent, "(local.get $", id, ")"]
    | LocalSet (id, value) -> 
        let valStr = pprintInstr (addi indent 1) value in
        join [indent2str indent, "(local.set $", id, "\n", valStr, ")"]
    | I32Add (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.add\n", s1, "\n", s2, ")"]
    | I32Eq (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.eq\n", s1, "\n", s2, ")"]
    | I32And (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.and\n", s1, "\n", s2, ")"]               
    | Call (fname, instructions) -> 
        let s = match instructions with [] 
            then ""
            else (concat "\n" (strJoin "\n" (map (pprintInstr (addi indent 1)) instructions))) in
        join [indent2str indent, "(call $", fname, s, ")"]
    | StructGet r -> 
        let s = pprintInstr (addi indent 1) r.value in 
        join [indent2str indent, "(struct.get $", r.typeAlias, " $", r.field, "\n", s, ")"]
    | StructNew r -> 
        let s = match r.values with []
            then ""
            else (concat "\n" (strJoin "\n" (map (pprintInstr (addi indent 1)) r.values))) in
        join [indent2str indent, "(struct.new $", r.typeAlias, s, ")"]
    | RefCast r -> 
        let sValue = pprintInstr (addi indent 1) r.value in
        join [indent2str indent, "(ref.cast\n", indent2str (addi 1 indent), "(ref $", r.typeAlias, ")\n", sValue, ")"]
    | RefTest r -> 
        let sValue = pprintInstr (addi indent 1) r.value in
        join [indent2str indent, "(ref.test\n", indent2str (addi 1 indent), "(ref $", r.typeAlias, ")\n", sValue, ")"]
    | CallIndirect r ->
        let addedIndent = indent2str (addi 1 indent) in 
        let typeStr = join [addedIndent, "(type $", r.typeString, ")"] in 
        let argsStr = strJoin "\n" (map (pprintInstr (addi 1 indent)) r.args) in
        let fpStr = pprintInstr (addi 1 indent) r.fp in
        join [indent2str indent, "(call_indirect\n", typeStr, "\n", argsStr, "\n", fpStr, ")"]
    | IfThenElse ite ->
        let indentPlusOne = addi indent 1 in 
        let cndStr = pprintInstr indentPlusOne ite.cond in
        let thnStr = pprintInstr indentPlusOne ite.thn in 
        let elsStr = pprintInstr indentPlusOne ite.els in 
        join [indent2str indent, "(if\n", cndStr, "\n", thnStr, "\n", elsStr, ")"]
    | Select s ->
        let indentPlusOne = addi indent 1 in 
        let cndStr = pprintInstr indentPlusOne s.cond in
        let thnStr = pprintInstr indentPlusOne s.thn in 
        let elsStr = pprintInstr indentPlusOne s.els in 
        join [indent2str indent, "(select\n", "\n", thnStr, "\n", elsStr, "\n", cndStr, ")"]

    sem pprintFunc indent = 
    | Function r -> 
        let argNameToArg = lam arg. join ["(param $", arg.name, " ", arg.typeString, ")"] in
        let pprintLocal = lam local. 
            join [indent2str (addi 1 indent), "(local $", local.name, " ", local.typeAlias, ")"] in
        let paramSep = match r.args with [] then "" else " " in 
        let params = strJoin " " (map argNameToArg r.args) in
        let sep = concat "\n" (indent2str 1) in
        let result = join ["(result ", r.resultTypeString, ")"] in 
        let localSep = match r.locals with [] then "" else "\n" in 
        let localStrs = strJoin "\n" (map pprintLocal r.locals) in
        let instrStrs = strJoin "\n" (map (pprintInstr (addi 1 indent)) r.instructions) in
        join [indent2str indent, "(func $", r.name, paramSep, params, " ", result, localSep, localStrs, sep, instrStrs, ")"]
    
    sem pprintMemory indent = 
    | Table t -> 
        join [indent2str indent, "(table ", int2string t.size, " ", t.typeString, ")"]
    | Elem e -> 
        let offsetStr = pprintInstr 0 e.offset in
        let funcNamesStr = strJoin " " (map (concat "$") e.funcNames) in
        join [indent2str indent, "(elem ", offsetStr, " ", funcNamesStr, ")"]

    sem pprintType indent = 
    | StructType r -> 
        let indent1 = indent2strnewline (addi 1 indent) in
        let indent2 = indent2strnewline (addi 2 indent) in
        let pprintField = lam field. 
            join ["(field $", field.name, " ", field.typeString, ")"] in
        let fieldsStr = match r.fields with []
            then ""
            else concat indent2 (strJoin indent2 (map pprintField r.fields)) in
        join [indent2str indent, "(type $", r.name, indent1, "(struct", fieldsStr, "))"]
    | FunctionType r -> 
        let param2str = lam p. join ["(param ", p, ")"] in 
        let paramStr = strJoin " " (map param2str r.paramTypeStrings) in 
        let resultStr = join ["(result ", r.resultTypeString, ")"] in
        join [indent2str indent, "(type $", r.name, " (func ", paramStr, " ", resultStr, "))"]

    sem pprintMod = 
    | Module m -> 
        let pprintExport = lam n. join ["    (export \"", n, "\" (func $", n, "))"] in
        -- let pprintExport = lam n. n in 
        let tableStr = pprintMemory 1 m.table in
        let elemStr = pprintMemory 1 m.elem in 
        let typeStr = strJoin "\n\n" (map (pprintType 1) m.types) in
        let funcStr = strJoin "\n\n" (map (pprintFunc 1) m.functions) in 
        let exportStr = strJoin "\n" (map pprintExport m.exports) in 

        join ["(module\n", tableStr, "\n\n", typeStr, "\n\n", funcStr, 
            "\n\n", elemStr, "\n", exportStr, ")"]
end

mexpr
use WasmPPrint in 
utest pprintInstr 0 (I32Const 10) with "(i32.const 10)" in 
utest pprintInstr 0 (LocalGet "x") with "(local.get $x)" in 
utest pprintInstr 0 (I32Add (I32Const 10, LocalGet "x")) with
     "(i32.add\n    (i32.const 10)\n    (local.get $x))" in 
utest pprintInstr 0 (Call ("f", [])) with "(call $f)" in 
utest pprintInstr 0 (Call ("f", [I32Const 10])) with "(call $f\n    (i32.const 10))" in 
utest pprintInstr 0 (Call ("f", [I32Const 10, I32Const 20])) with "(call $f\n    (i32.const 10)\n    (i32.const 20))" in 
utest pprintInstr 0 (StructGet {typeAlias="foo", field="bar", value=LocalGet "s"}) with
    "(struct.get $foo $bar\n    (local.get $s))" in
utest pprintType 0 (StructType {name="point", fields=[{name="x", typeString="i32"}, {name="y", typeString="i32"}]}) with
    "(type $point\n    (struct\n        (field $x i32)\n        (field $y i32)))" in
utest pprintType 0 (StructType {name="empty", fields=[]}) with
    "(type $empty\n    (struct))" in
utest pprintMemory 1 (Table {size = 5, typeString = "funcref"}) with
    "    (table 5 funcref)" in
utest pprintMemory 1 (Elem {offset=I32Const 0, funcNames=["f", "g", "h"]}) with
    "    (elem (i32.const 0) $f $g $h)" in 
utest pprintType 1 (FunctionType {
    name="generic-type",
    paramTypeStrings=["anyref", "anyref"],
    resultTypeString="anyref"
}) with "    (type $generic-type (func (param anyref) (param anyref) (result anyref)))" in 
let eq33 = I32Eq (I32Const 3, I32Const 3) in 
utest pprintInstr 1 eq33 with 
    "    (i32.eq\n        (i32.const 3)\n        (i32.const 3))" in 
let ite = IfThenElse {cond = eq33, thn = I32Const 23, els = I32Const 42} in
utest pprintInstr 0 ite with "(if\n    (i32.eq\n        (i32.const 3)\n        (i32.const 3))\n    (i32.const 23)\n    (i32.const 42))" in 
()