include "mexpr/pprint.mc"

include "mexpr/ast.mc"
include "mexpr/info.mc"
include "mexpr/type.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

include "string.mc"
include "seq.mc"

lang WasmAST
    syn Instr =
    | I32Const Int
    | LocalGet String
    | I32Add
    | CallIndirect Int
    | Call String

    syn Func = 
    | Function {
        alias: String,
        args: [String],
        instructions: [Instr]
    }

    syn Mod = 
    | Module {
        functions: [Func],
        exports: [String]
    }
end

-- Helper Functions for Pretty Printing
let pWrap = lam s. join ["(", s, ")"]
let printArg = lam arg. (join ["(param $", arg, " i32)"])
let str2export = lam s. (join ["(export \"", s, "\" (func $", s, "))"])

lang WasmPrettyPrint = WasmAST
    sem pprintInstr: Instr -> String
    sem pprintInstr = 
    | I32Const(i) -> (concat "i32.const " (int2string i))
    | I32Add() -> "i32.add"
    | LocalGet(id) -> (concat "local.get $" id)
    | CallIndirect(n) -> (concat "call_indirect " (int2string n))
    | Call(id) -> (concat "call $" id)
    | other -> "Unknown instruction!"

    sem pprintFunc: Func -> String
    sem pprintFunc = 
    | Function r -> (join [ 
        "(func $",
        r.alias,
        (match r.args with [] then "" else " "),
        (strJoin " " (map printArg r.args)),
        " (result i32) ",
        (strJoin "\n" (map pWrap (map pprintInstr r.instructions))),
    ")"])
    | other -> error "Unknown Func!"

    sem pprintMod: Mod -> String
    sem pprintMod = 
    | Module r -> (strJoin "\n" [
        "(module ",
        (strJoin "\n" (map pprintFunc r.functions)),
        (strJoin "\n" (map str2export r.exports)),
        ")"
    ])
    | other -> error "Unknown Mod!"
end

-- Helper functions for compilation
type Context = {
    nextFunctionId: Int, 
    functions: [use WasmAST in Func]
}
let emptyCtx = {nextFunctionId = 0, functions = []}
let ctxAddedFunc = lam ctx: Context. lam f: (use WasmAST in Func).
    {ctx with functions = (cons f ctx.functions), 
              nextFunctionId = addi ctx.nextFunctionId 1}
let lastFunctionName = lam ctx : Context. 
    use WasmAST in 
    match (head ctx.functions) with Function {alias = a, args = _, instructions = _}
        then a
        else error "???"
let pprintCtx = lam ctx: Context .
    use WasmPrettyPrint in
    strJoin "\n" (cons (int2string ctx.nextFunctionId) (map pprintFunc ctx.functions))

lang WasmCompile = MExprAst + WasmAST
    sem compileCtx : Context -> Expr -> (Context, [Instr])
    sem compileCtx ctx =
    | TmConst { val = c, info = _ } -> 
        match c with CInt {val = v} 
            then (ctx, [I32Const v])
        else match c with CAddi _ then (ctx, [Call "addi"])
        else error "TmConst(???)"
    | TmVar r -> (ctx, [LocalGet r.ident.0])
    | TmLam r -> 
        match compileCtx ctx r.body with (ctx2, instrs)
        then
            let fid = (concat "f" (int2string ctx2.nextFunctionId)) in
            let f = Function {
                alias = fid,
                args = [r.ident.0],
                instructions = instrs
            } in
            let ctx3 = ctxAddedFunc ctx2 f in
            (ctx3, [Call (lastFunctionName ctx3)])
        else error "Could not compile TmLam"
    | TmApp { lhs = l, rhs = r} -> 
        let rresult = compileCtx ctx r in 
        match rresult with (rctx, rinstrs)
            then let lresult = compileCtx rctx l in
            match lresult with (lrctx, linstrs)
                then (lrctx, join [rinstrs, linstrs])
                else error "???"
            else error "???"
    | whatever -> error "I don't know this."

    sem compile: Expr -> Mod
    sem compile = | expr -> let result = compileCtx emptyCtx expr in
        match result with (ctx, is)
            then let main = Function {alias="main", args=[], instructions=is} in
            Module {functions = cons main ctx.functions, exports=["main"]}
            else error "???"
end

lang WasmCompilePPrint = WasmCompile + WasmPrettyPrint end

let compileMCoreToWasm = lam ast.
    -- use MExprPrettyPrint in
    -- printLn (expr2str ast);
    use WasmCompilePPrint in
    printLn (pprintMod (compile ast));
    ""

mexpr
use WasmCompilePPrint in 
let mol = (Function({
    args=[],
    alias="meaningOfLife",
    instructions=[I32Const 42]
})) in
-- let add123 = (addi_ (int_ 1) (addi_ (int_ 2) (int_ 3))) in
let f1 = (app_ (lam_ "x" tyint_ (addi_ (var_ "x") (int_ 1))) (int_ 3)) in
utest ctxAddedFunc emptyCtx mol with {nextFunctionId = 1, functions=[mol]} in
utest lastFunctionName (ctxAddedFunc emptyCtx mol) with "meaningOfLife" in
(printLn (pprintMod (compile f1)))