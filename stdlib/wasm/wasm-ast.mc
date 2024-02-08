lang WasmAST
    syn Instr =
    | I32Const Int
    | I32Add (Instr, Instr)
    | I32Sub (Instr, Instr)
    | I32Mul (Instr, Instr)
    | I32And (Instr, Instr)
    | I32Eq (Instr, Instr)
    | I32Ne (Instr, Instr)
    | LocalGet String
    | LocalSet (String, Instr)
    | GlobalGet String
    | Call (String, [Instr])
    | Loop {
        ident: String,
        body: [Instr]
    }
    | BrIf {
        ident: String,
        cond: Instr
    }
    | StructGet {
        structIdent: String,
        field: String,
        value: Instr
    }
    | StructNew {
        structIdent: String,
        values: [Instr]
    }
    | ArrayNew {
        tyIdent: String,
        initValue: Instr,
        size: Instr
    }
    | ArrayGet {
        tyIdent: String,
        value: Instr,
        index: Instr
    }
    | ArraySet {
        tyIdent: String,
        value: Instr,
        index: Instr,
        value2: Instr
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
    | ArrayTypeDef {
        ident: String,
        paramTys: [WasmType]
    }
    | GlobalDef {
        ident: String,
        ty: WasmType, 
        initValue: Instr
    }

    syn WasmType = 
    | Tyi32 ()
    | Tyi64 ()
    | Tyf32 ()
    | Tyf64 ()
    | Array WasmType
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