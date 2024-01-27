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

lang DoodleCompile = MExprAst + WasmAST
    sem compileCtx : Context -> Expr -> (Context, [Instr])
    sem compileCtx ctx =
    | TmConst { val = c, info = _ } -> 
        match c with CInt {val = v} 
            then (let newCtx = ctxAddedFunc ctx (Function {
                args=[], 
                alias=(concat "f" (int2string ctx.nextFunctionId)),
                instructions = [I32Const v]
            }) in (newCtx, [Call (lastFunctionName newCtx)])) 
        else match c with CAddi _ then (ctx, [Call "addi"])
        else error "TmConst(???)"
    -- | TmVar { ident = (id, _) } -> (concat "TmVar_" id)
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

mexpr
use WasmAST in 

let pprintInstr = lam ast. 
    join ["(", 
        (match ast with I32Const(i) then (concat "i32.const " (int2string i))
        else match ast with I32Add() then "i32.add"
        else match ast with LocalGet(id) then (concat "local.get $" id)
        else match ast with CallIndirect(n) then (concat "call_indirect " (int2string n))
        else match ast with Call(id) then (concat "call $" id)
        else error "Unknown WasmAST instruction"), ")"]
in

let pprintFunc = lam f. 
    let printArg = lam arg. (join ["(param $", arg, " i32)"]) in
    match f with Function(r) then (join [ 
        "(func $",
        r.alias,
        (match r.args with [] then "" else " "),
        (strJoin " " (map printArg r.args)),
        " (result i32) ",
        (strJoin "\n" (map pprintInstr r.instructions)),
        ")"])
    else error "Unknown WasmAST function"
    in

-- let pprintTableFunc = lam f. 
--     match f with Function {args = _, instructions = is, name=n} 
--         then join ["(func $", n, " " strJoin " " (map pprintInstr is), ")"]
--         else error "Cannot match TableFunction"
-- in  

let pprintCtx = lam ctx: Context .
    strJoin "\n" (cons (int2string ctx.nextFunctionId) (map pprintFunc ctx.functions))
in

let pprintMod = lam m. 
    let str2export = lam s. (join ["(export \"", s, "\" (func $", s, "))"]) in 
    match m with Module(r) then (strJoin "\n" [
        "(module ",
        (strJoin "\n" (map pprintFunc r.functions)),
        (strJoin "\n" (map str2export r.exports)),
        ")"
    ])
    else error "Unknown WasmAST module"
in
let mol = (Function({
    args=[],
    alias="meaningOfLife",
    instructions=[I32Const 42]
})) in
let add123 = (addi_ (int_ 1) (addi_ (int_ 2) (int_ 3))) in
utest ctxAddedFunc emptyCtx mol with {nextFunctionId = 1, functions=[mol]} in
utest lastFunctionName (ctxAddedFunc emptyCtx mol) with "meaningOfLife" in
use DoodleCompile in
-- (match (compileCtx emptyCtx (int_ 10)) with (ctx, is)
--     then printLn (pprintCtx ctx); printLn (strJoin " " (map pprintInstr is))
--     else printLn "Something else");
-- (match (compileCtx emptyCtx (addi_ (int_ 1) (int_ 10))) with (ctx, is)
--     then printLn (pprintCtx ctx); printLn (strJoin " " (map pprintInstr is))
--     else printLn "Something else");
-- (match (compileCtx emptyCtx (addi_ (int_ 1) (addi_ (int_ 2) (int_ 3)))) with (ctx, is)
--     then printLn (pprintCtx ctx); printLn (strJoin " " (map pprintInstr is))
--     else printLn "Something else");
(printLn (pprintMod (compile add123)))
-- printLn (compile emptyCtx (int_ 10));
-- printLn (compile emptyCtx (addi_ (int_ 1) (int_ 4)))

-- printLn (expr2str (int_ 10))
-- utest (int_ 10) with (TmConst {val = (CInt {val=10}), ty = TyInt(), info = NoInfo()}) in ()
-- utest (int_ 10) with (int_ 10) in ()
