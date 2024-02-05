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
    | RefTest {
        typeAlias: String,
        value: Instr
    }
    | CallIndirect {
        typeString: String,
        args: [Instr],
        fp: Instr
    }
    | IfThenElse {
        cond: Instr,
        thn: Instr,
        els: Instr
    }
    | Select {
        cond: Instr,
        thn: Instr,
        els: Instr
    }

    syn Func = 
    | Function {
        name: String,
        args: [{name: String, typeString: String}],
        locals: [{name: String, typeAlias: String}],
        resultTypeString: String,
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
    | FunctionType {
        name: String,
        paramTypeStrings: [String],
        resultTypeString: String
    }

    syn WasmMemory = 
    | Table {size: Int, typeString: String}
    | Elem {offset: Instr, funcNames: [String]}

    syn Mod = 
    | Module {
        functions: [Func],
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