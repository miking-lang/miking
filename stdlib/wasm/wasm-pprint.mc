include "wasm-ast.mc"
include "string.mc"
include "seq.mc"
include "common.mc"

let indent2str = lam indent. make (muli indent 4) ' '
let indent2strnewline = lam indent. concat "\n" (make (muli indent 4) ' ')

lang WasmPPrint = WasmAST
    sem pprintWasmType: WasmType -> String
    sem pprintWasmType = 
    | Tyi32 () -> "i32"
    | Tyi64 () -> "i64"
    | Tyf32 () -> "f32"
    | Tyf64 () -> "f64"
    | Anyref () -> "anyref"
    | Ref ident -> join ["(ref $", ident, ")"]

    sem pprintInstr: Int -> Instr -> String
    sem pprintInstr indent = 
    | I32Const i -> join [indent2str indent, "(i32.const ", (int2string i), ")"]
    | LocalGet id -> join [indent2str indent, "(local.get $", id, ")"]
    | GlobalGet id -> join [indent2str indent, "(global.get $", id, ")"]
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
        join [indent2str indent, "(struct.get $", r.structIdent, " $", r.field, "\n", s, ")"]
    | StructNew r -> 
        let s = match r.values with []
            then ""
            else (concat "\n" (strJoin "\n" (map (pprintInstr (addi indent 1)) r.values))) in
        join [indent2str indent, "(struct.new $", r.structIdent, s, ")"]
    | ArrayNew r -> 
        let indent1 = addi 1 indent in 
        let tyStr = cons '$' r.tyIdent in 
        let initStr = pprintInstr indent1 r.initValue in 
        let sizeStr = pprintInstr indent1 r.size in 
        join [indent2str indent, "(array.new ", tyStr, "\n", initStr, "\n", sizeStr, ")"]
    | ArrayGet r -> 
        let indent1 = addi 1 indent in 
        let tyStr = cons '$' r.tyIdent in 
        let valueStr = pprintInstr indent1 r.value in 
        let indexStr = pprintInstr indent1 r.index in 
        join [indent2str indent, "(array.get ", tyStr, "\n", valueStr, "\n", indexStr, ")"]
    | ArraySet r -> 
        let indent1 = addi 1 indent in 
        let tyStr = cons '$' r.tyIdent in 
        let valueStr = pprintInstr indent1 r.value in 
        let value2Str = pprintInstr indent1 r.value2 in 
        let indexStr = pprintInstr indent1 r.index in 
        join [indent2str indent, "(array.set ", tyStr, "\n", valueStr, "\n", indexStr, "\n", value2Str, ")"]
    | RefCast r -> 
        let sValue = pprintInstr (addi indent 1) r.value in
        let sTy = pprintWasmType r.ty in 
        join [indent2str indent, "(ref.cast\n", indent2str (addi 1 indent), sTy, "\n", sValue, ")"]
    | RefTest r -> 
        let sValue = pprintInstr (addi indent 1) r.value in
        let sTy = pprintWasmType r.ty in 
        join [indent2str indent, "(ref.test\n", indent2str (addi 1 indent), sTy, "\n", sValue, ")"]
    | CallIndirect r ->
        let addedIndent = indent2str (addi 1 indent) in 
        let typeStr = join [addedIndent, "(type $", r.ty, ")"] in 
        let argsStr = strJoin "\n" (map (pprintInstr (addi 1 indent)) r.args) in
        let fpStr = pprintInstr (addi 1 indent) r.fp in
        join [indent2str indent, "(call_indirect\n", typeStr, "\n", argsStr, "\n", fpStr, ")"]
    | IfThenElse ite ->
        let indentPlusOne = addi indent 1 in 
        let cndStr = pprintInstr indentPlusOne ite.cond in
        let thnStr = strJoin "\n" (map (pprintInstr indentPlusOne) ite.thn) in 
        let thnStr = join [indent2str indentPlusOne, "(then\n", thnStr, ")"] in 
        let elsStr = strJoin "\n" (map (pprintInstr indentPlusOne) ite.els) in 
        let elsStr = join [indent2str indentPlusOne, "(else\n", elsStr, ")"] in 
        join [indent2str indent, "(if\n", cndStr, "\n", thnStr, "\n", elsStr, ")"]
    | Select s ->
        let indentPlusOne = addi indent 1 in 
        let cndStr = pprintInstr indentPlusOne s.cond in
        let thnStr = pprintInstr indentPlusOne s.thn in 
        let elsStr = pprintInstr indentPlusOne s.els in 
        join [indent2str indent, "(select\n", "\n", thnStr, "\n", elsStr, "\n", cndStr, ")"]

    sem pprintDef indent = 
    | FunctionDef r -> 
        let pprintArg = lam arg. 
            let tyStr = pprintWasmType arg.ty in 
            join ["(param $", arg.ident, " ", tyStr, ")"] in 
        let pprintLocal = lam local. 
            let tyStr = pprintWasmType local.ty in 
            let prefix = indent2str (addi 1 indent) in 
            join [prefix, "(local $", local.ident, " ", tyStr, ")"] in 
        let argsSep = match r.args with []
            then ""
            else " " in
        let argsStr = strJoin " " (map pprintArg r.args) in
        let resultStr = join ["(result ", pprintWasmType r.resultTy, ")"] in 
        let localStr = strJoin "\n" (map pprintLocal r.locals) in
        let bodyStr = strJoin "\n" (map (pprintInstr (addi 1 indent)) r.instructions) in
        join ["(func $", r.ident, argsSep, argsStr, " ", resultStr, "\n", localStr, "\n", bodyStr, ")"]
    | StructTypeDef r -> 
        let indent1 = indent2strnewline (addi 1 indent) in
        let indent2 = indent2strnewline (addi 2 indent) in
        let pprintField = lam field. 
            join ["(field $", field.ident, " ", (pprintWasmType field.ty), ")"] in
        let fieldsStr = match r.fields with []
            then ""
            else concat indent2 (strJoin indent2 (map pprintField r.fields)) in
        join [indent2str indent, "(type $", r.ident, indent1, "(struct", fieldsStr, "))"]
    | FunctionTypeDef r -> 
        let param2str = lam ty. join ["(param ", pprintWasmType ty, ")"] in 
        let paramStr = strJoin " " (map param2str r.paramTys) in 
        let resultStr = join ["(result ", pprintWasmType r.resultTy, ")"] in
        join [indent2str indent, "(type $", r.ident, " (func ", paramStr, " ", resultStr, "))"]

    sem pprintMemory indent = 
    | Table t -> 
        join [indent2str indent, "(table ", int2string t.size, " ", t.typeString, ")"]
    | Elem e -> 
        let offsetStr = pprintInstr 0 e.offset in
        let funcNamesStr = strJoin " " (map (concat "$") e.funcNames) in
        join [indent2str indent, "(elem ", offsetStr, " ", funcNamesStr, ")"]
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
utest pprintInstr 0 (StructGet {structIdent="foo", field="bar", value=LocalGet "s"}) with
    "(struct.get $foo $bar\n    (local.get $s))" in
utest pprintDef 0 (StructTypeDef {ident="point", fields=[{ident="x", ty=Tyi32 () }, {ident="y", ty=Tyi32 ()}]}) with
    "(type $point\n    (struct\n        (field $x i32)\n        (field $y i32)))" in
utest pprintDef 0 (StructTypeDef {ident="empty", fields=[]}) with
    "(type $empty\n    (struct))" in
utest pprintMemory 1 (Table {size = 5, typeString = "funcref"}) with
    "    (table 5 funcref)" in
utest pprintMemory 1 (Elem {offset=I32Const 0, funcNames=["f", "g", "h"]}) with
    "    (elem (i32.const 0) $f $g $h)" in 
utest pprintDef 1 (FunctionTypeDef {
    ident="generic-type",
    paramTys=[Anyref(), Anyref()],
    resultTy=Anyref()
}) with "    (type $generic-type (func (param anyref) (param anyref) (result anyref)))" in 
let eq33 = I32Eq (I32Const 3, I32Const 3) in 
utest pprintInstr 1 eq33 with 
    "    (i32.eq\n        (i32.const 3)\n        (i32.const 3))" in 
-- let ite = IfThenElse {cond = eq33, thn = [I32Const 23], els = [I32Const 42]} in
-- utest pprintInstr 0 ite with "(if\n    (i32.eq\n        (i32.const 3)\n        (i32.const 3))\n    (then (i32.const 23))\n    (i32.const 42))" in 
()