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

    sem pprintFunc = 
    | Function r -> 
        let argNameToArg = lam arg. join ["(param $", arg, " anyref)"] in
        let pprintLocal = lam local. 
            join ["(local $", local.name, " ", local.typeAlias, ")"] in
        let params = strJoin " " (map argNameToArg r.args) in
        let result = "(result anyref)" in
        let sep = concat "\n" (indent2str 1) in
        let localStrs = strJoin "\n    " (map pprintLocal r.locals) in
        let instrStrs = strJoin sep (map (pprintInstr 1) r.instructions) in
        join ["(func $", r.name, " ", params, " ", result, "\n    ", localStrs, sep, instrStrs, ")"]
    
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

    sem pprintMod = 
    | Module m -> 
        let pprintExport = lam n. join ["    (export \"", n, "\" (func $", n, "))"] in
        -- let pprintExport = lam n. n in 
        let tableStr = pprintMemory 1 m.table in
        let elemStr = pprintMemory 1 m.elem in 
        let typeStr = strJoin "\n" (map (pprintType 1) m.types) in
        let funcStr = strJoin "\n\n" (map pprintFunc m.functions) in 
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
()