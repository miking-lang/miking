lang WasmAST
    syn Instr =
    | I32Const Int
    | LocalGet String
    | LocalSet (String, Instr)
    | I32Add (Instr, Instr)
    -- | CallIndirect Instr Instr Instr
    | Call (String, [Instr])
    | StructGet {
        typeAlias: String,
        value: Instr,
        field: String
    }
    | StructNew {
        typeAlias: String,
        values: [Instr]
    }
    | RefCast {
        typeAlias: String,
        value: Instr
    }

    syn Func = 
    | Function {
        name: String,
        args: [String],
        locals: [{name: String, typeAlias: String}],
        instructions: [Instr]
    }

    syn WasmType = 
    | StructType {
        name: String,
        fields: [{
            name: String,
            typeString: String
        }]
    }

    syn Mod = 
    | Module {
        functions: [Func],
        exports: [String]
    }
end


mexpr 
use WasmAST in 
utest I32Const 10 with I32Const 10 in
utest I32Add (I32Const 10, I32Const 1) with I32Add (I32Const 10, I32Const 1) in
()