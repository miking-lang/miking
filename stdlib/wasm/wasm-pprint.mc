include "wasm-ast.mc"
include "string.mc"
include "seq.mc"
include "common.mc"

let indent2str = lam indent. make (muli indent 4) ' '
let indent2strnewline = lam indent. concat "\n" (make (muli indent 4) ' ')

lang WasmPPrint = WasmAST
    sem pprintName : Name -> String
    sem pprintName = 
    | name -> 
        match nameGetSym name with Some s
        then concat (nameGetStr name) (int2string (sym2hash s))
        else nameGetStr name

    sem pprintWasmType: WasmType -> String
    sem pprintWasmType = 
    | Tyi32 () -> "i32"
    | Tyi64 () -> "i64"
    | Tyf32 () -> "f32"
    | Tyf64 () -> "f64"
    | Anyref () -> "anyref"
    | I31Ref () -> "i31ref"
    | Ref ident -> join ["(ref $", pprintName ident, ")"]

    sem pprintInstr: Int -> Instr -> String
    sem pprintInstr indent = 
    | I32Const i -> join [indent2str indent, "(i32.const ", (int2string i), ")"]
    | LocalGet id -> join [indent2str indent, "(local.get $", pprintName id, ")"]
    | GlobalGet id -> join [indent2str indent, "(global.get $", pprintName id, ")"]
    | Unreachable _ -> concat (indent2str indent) "(unreachable)"
    | LocalSet (id, value) -> 
        let valStr = pprintInstr (addi indent 1) value in
        join [indent2str indent, "(local.set $", pprintName id, "\n", valStr, ")"]
    | I32Add (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.add\n", s1, "\n", s2, ")"]
    | I32Sub (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.sub\n", s1, "\n", s2, ")"]
    | I32Mul (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.mul\n", s1, "\n", s2, ")"]                
    | I32Eq (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.eq\n", s1, "\n", s2, ")"]
    | I32Ne (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.ne\n", s1, "\n", s2, ")"]
    | I32LtS (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.lt_s\n", s1, "\n", s2, ")"]
    | I32GtS (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.gt_s\n", s1, "\n", s2, ")"]
    | I32LeS (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.le_s\n", s1, "\n", s2, ")"]
    | I32GeS (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.ge_s\n", s1, "\n", s2, ")"]
    | I32And (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.and\n", s1, "\n", s2, ")"]      
    | I32DivS (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.div_s\n", s1, "\n", s2, ")"]   
    | I32RemS (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.rem_s\n", s1, "\n", s2, ")"]                            
    | I32Shl (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.shl\n", s1, "\n", s2, ")"]               
    | I32ShrS (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.shr_s\n", s1, "\n", s2, ")"]               
    | I32ShrU (i1, i2) -> 
        let s1 = pprintInstr (addi indent 1) i1 in
        let s2 = pprintInstr (addi indent 1) i2 in 
        join [indent2str indent, "(i32.shr_u\n", s1, "\n", s2, ")"]               
    | Call (fname, instructions) -> 
        let s = match instructions with [] 
            then ""
            else (concat "\n" (strJoin "\n" (map (pprintInstr (addi indent 1)) instructions))) in
        join [indent2str indent, "(call $", pprintName fname, s, ")"]
    | StructGet r -> 
        let s = pprintInstr (addi indent 1) r.value in 
        join [indent2str indent, "(struct.get $", pprintName r.structIdent, " $", pprintName r.field, "\n", s, ")"]
    | StructNew r -> 
        let s = match r.values with []
            then ""
            else (concat "\n" (strJoin "\n" (map (pprintInstr (addi indent 1)) r.values))) in
        join [indent2str indent, "(struct.new $", pprintName r.structIdent, s, ")"]
    | ArrayNew r -> 
        let indent1 = addi 1 indent in 
        let tyStr = cons '$' (pprintName r.tyIdent) in 
        let initStr = pprintInstr indent1 r.initValue in 
        let sizeStr = pprintInstr indent1 r.size in 
        join [indent2str indent, "(array.new ", tyStr, "\n", initStr, "\n", sizeStr, ")"]
    | ArrayGet r -> 
        let indent1 = addi 1 indent in 
        let tyStr = cons '$' (pprintName r.tyIdent) in 
        let valueStr = pprintInstr indent1 r.value in 
        let indexStr = pprintInstr indent1 r.index in 
        join [indent2str indent, "(array.get ", tyStr, "\n", valueStr, "\n", indexStr, ")"]
    | ArraySet r -> 
        let indent1 = addi 1 indent in 
        let tyStr = cons '$' (pprintName r.tyIdent) in 
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
        let typeStr = join [addedIndent, "(type $", pprintName r.ty, ")"] in 
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
    | Loop l -> 
        let bodyStr = strJoin "\n" (map (pprintInstr (addi indent 1)) l.body) in
        join [indent2str indent, "(loop $", pprintName l.ident, "\n", bodyStr, ")"]
    | BrIf r ->
        let condStr = pprintInstr (addi 1 indent) r.cond in 
        join [indent2str indent, "(br_if $", pprintName r.ident, "\n", condStr, ")"]
    | Return instr ->
        let instrStr = pprintInstr (addi 1 indent) instr in 
        join [indent2str indent, "(return\n", instrStr, ")"]
    | I31Cast instr -> 
        let instrStr = pprintInstr (addi 1 indent) instr in 
        join [indent2str indent, "(ref.i31\n", instrStr, ")"]
    | I31GetU instr -> 
            let instrStr = pprintInstr (addi 1 indent) instr in 
            join [indent2str indent, "(i31.get_u\n", instrStr, ")"]
    | I31GetS instr -> 
            let instrStr = pprintInstr (addi 1 indent) instr in 
            join [indent2str indent, "(i31.get_s\n", instrStr, ")"]

    sem pprintDef indent = 
    | FunctionDef r -> 
        let pprintArg = lam arg. 
            let tyStr = pprintWasmType arg.ty in 
            join ["(param $", pprintName arg.ident, " ", tyStr, ")"] in 
        let pprintLocal = lam local. 
            let tyStr = pprintWasmType local.ty in 
            let prefix = indent2str (addi 1 indent) in 
            join [prefix, "(local $", pprintName local.ident, " ", tyStr, ")"] in 
        let argsSep = match r.args with []
            then ""
            else " " in
        let argsStr = strJoin " " (map pprintArg r.args) in
        let resultStr = join ["(result ", pprintWasmType r.resultTy, ")"] in 
        let localStr = strJoin "\n" (map pprintLocal r.locals) in
        let bodyStr = strJoin "\n" (map (pprintInstr (addi 1 indent)) r.instructions) in
        join [indent2str indent, "(func $", pprintName r.ident, argsSep, argsStr, " ", resultStr, "\n", localStr, "\n", bodyStr, ")"]
    | StructTypeDef r -> 
        let indent1 = indent2strnewline (addi 1 indent) in
        let indent2 = indent2strnewline (addi 2 indent) in
        let pprintField = lam field. 
            join ["(field $", pprintName field.ident, " ", (pprintWasmType field.ty), ")"] in
        let fieldsStr = match r.fields with []
            then ""
            else concat indent2 (strJoin indent2 (map pprintField r.fields)) in
        join [indent2str indent, "(type $", pprintName r.ident, indent1, "(struct", fieldsStr, "))"]
    | FunctionTypeDef r -> 
        let param2str = lam ty. join ["(param ", pprintWasmType ty, ")"] in 
        let paramStr = strJoin " " (map param2str r.paramTys) in 
        let resultStr = join ["(result ", pprintWasmType r.resultTy, ")"] in
        join [indent2str indent, "(type $", pprintName r.ident, " (func ", paramStr, " ", resultStr, "))"]
    | ArrayTypeDef r -> 
        let param2str = lam paramTy. 
            join ["(mut ", pprintWasmType paramTy, ")"] in 
        let paramsStr = strJoin " " (map param2str r.paramTys) in 
        join [indent2str indent, "(type $", pprintName r.ident, " (array ", paramsStr, "))"]
    | GlobalDef r ->
        let initValueStr = pprintInstr (addi indent 1) r.initValue in
        let tyStr = pprintWasmType r.ty in 
        join [indent2str indent, "(global $", pprintName r.ident, " ", tyStr, "\n", initValueStr, ")"]

    sem pprintMemory indent = 
    | Table t -> 
        join [indent2str indent, "(table ", int2string t.size, " ", t.typeString, ")"]
    | Elem e -> 
        let offsetStr = pprintInstr 0 e.offset in
        let funcNames = map pprintName e.funcNames in 
        let funcNamesStr = strJoin " " (map (concat "$") funcNames) in
        join [indent2str indent, "(elem ", offsetStr, " ", funcNamesStr, ")"]

    sem pprintMod = 
    | Module m -> 
        let pprintImport = lam r. join [
            indent2str 1, 
            "(import \"",
            r.jsObjIdent, 
            "\" \"",
            r.jsFieldIdent, 
            "\" (func $",
            pprintName r.wasmIdent,
            "))"
        ] in 
        let pprintExport = lam n. join ["    (export \"", pprintName n, "\" (func $", pprintName n, "))"] in
        let tableStr = pprintMemory 1 m.table in
        let elemStr = pprintMemory 1 m.elem in 
        let defsStr = strJoin "\n\n" (map (pprintDef 1) m.definitions) in 
        let exportStr = strJoin "\n" (map pprintExport m.exports) in 
        let importStr= strJoin "\n" (map pprintImport m.imports) in 

        join ["(module\n", tableStr, "\n", importStr, "\n\n", defsStr, 
            "\n\n", elemStr, "\n", exportStr, ")"]
end

mexpr
use WasmPPrint in 
-- Test i31 
utest pprintWasmType (I31Ref ()) with "i31ref" in 
utest pprintInstr 0 (I31Cast (I32Const 10)) with "(ref.i31\n    (i32.const 10))" in
utest pprintInstr 0 (I31GetS (LocalGet (nameNoSym "x"))) with "(i31.get_s\n    (local.get $x))" in
utest pprintInstr 0 (I31GetU (LocalGet (nameNoSym "x"))) with "(i31.get_u\n    (local.get $x))" in

utest pprintInstr 0 (I32Const 10) with "(i32.const 10)" in 
utest pprintInstr 0 (LocalGet (nameNoSym "x")) with "(local.get $x)" in 
utest pprintInstr 0 (I32Add (I32Const 10, LocalGet (nameNoSym "x"))) with
     "(i32.add\n    (i32.const 10)\n    (local.get $x))" in 
utest pprintInstr 0 (Call ((nameNoSym "f"), [])) with "(call $f)" in 
utest pprintInstr 0 (Call ((nameNoSym "f"), [I32Const 10])) with "(call $f\n    (i32.const 10))" in 
utest pprintInstr 0 (Call ((nameNoSym "f"), [I32Const 10, I32Const 20])) with "(call $f\n    (i32.const 10)\n    (i32.const 20))" in 
utest pprintInstr 0 (StructGet {structIdent=(nameNoSym "foo"), field=(nameNoSym "bar"), value=LocalGet (nameNoSym "s")}) with
    "(struct.get $foo $bar\n    (local.get $s))" in
utest pprintDef 0 (StructTypeDef {
        ident=(nameNoSym "point"), 
        fields=[{ident=(nameNoSym "x"), ty=Tyi32 () 
    }, {ident=(nameNoSym "y"), ty=Tyi32 ()}]}) with
    "(type $point\n    (struct\n        (field $x i32)\n        (field $y i32)))" in
utest pprintDef 0 (StructTypeDef {ident=(nameNoSym "empty"), fields=[]}) with
    "(type $empty\n    (struct))" in
utest pprintMemory 1 (Table {size = 5, typeString = "funcref"}) with
    "    (table 5 funcref)" in
utest pprintMemory 1 (Elem {offset=I32Const 0, funcNames=(map nameNoSym ["f", "g", "h"])}) with
    "    (elem (i32.const 0) $f $g $h)" in 
utest pprintDef 1 (FunctionTypeDef {
    ident=(nameNoSym "generic-type"),
    paramTys=[Anyref(), Anyref()],
    resultTy=Anyref()
}) with "    (type $generic-type (func (param anyref) (param anyref) (result anyref)))" in 
-- let eq33 = I32Eq (I32Const 3, I32Const 3) in 
-- utest pprintInstr 1 eq33 with 
--     "    (i32.eq\n        (i32.const 3)\n        (i32.const 3))" in 
-- let ite = IfThenElse {cond = eq33, thn = [I32Const 23], els = [I32Const 42]} in
-- utest pprintInstr 0 ite with "(if\n    (i32.eq\n        (i32.const 3)\n        (i32.const 3))\n    (then (i32.const 23))\n    (i32.const 42))" in 
()