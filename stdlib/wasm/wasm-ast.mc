lang WasmAST
    syn Instr =
    | I32Const Int
    | I32Add (Instr, Instr)
    | I32And (Instr, Instr)
    | I32Eq (Instr, Instr)
    | LocalGet String
    | LocalSet (String, Instr)
    | Call (String, [Instr])
    | StructGet {
        structIdent: String,
        field: String,
        value: Instr
    }
    | StructNew {
        structIdent: String,
        values: [Instr]
    }
    | RefCast {
        ty: WasmType,
        value: Instr
    }
    | RefTest {
        ty: WasmType,
        value: Instr
    }
    | CallIndirect {
        ty: String,
        args: [Instr],
        fp: Instr
    }
    | IfThenElse {
        cond: Instr,
        thn: [Instr],
        els: [Instr]
    }
    | Select {
        cond: Instr,
        thn: Instr,
        els: Instr
    }

    syn Def = 
    | FunctionDef {
        ident: String,
        args: [{ident: String, ty: WasmType}],
        locals: [{ident: String, ty: WasmType}],
        resultTy: WasmType,
        instructions: [Instr]
    }
    | StructTypeDef {
        ident: String,
        fields: [{
            ident: String,
            ty: WasmType
        }]
    }
    | FunctionTypeDef {
        ident: String,
        paramTys: [WasmType],
        resultTy: WasmType
    }

    syn WasmType = 
    | Tyi32 ()
    | Tyi64 ()
    | Tyf32 ()
    | Tyf64 ()
    | Anyref ()
    | Ref String

    syn WasmMemory = 
    | Table {size: Int, typeString: String}
    | Elem {offset: Instr, funcNames: [String]}

    syn Mod = 
    | Module {
        definitions: [Def],
        table: WasmMemory, 
        elem: WasmMemory, 
        types: [WasmType],
        exports: [String]
    }
end


mexpr 
use WasmAST in 
utest I32Const 10 with I32Const 10 in
utest I32Add (I32Const 10, I32Const 1) with I32Add (I32Const 10, I32Const 1) in
()