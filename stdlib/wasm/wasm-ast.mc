include "string.mc"

lang WasmAST
    syn Instr =
    | I32Const Int
    | LocalGet String
    | I32Add

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



mexpr 
use WasmAST in 

let pprintInstr = lam ast. 
    match ast with I32Const(i) then (concat "i32.const " (int2string i))
    else match ast with I32Add() then "i32.add"
    else match ast with LocalGet(id) then (concat "local.get $" id)
    else error "Unknown WasmAST instruction" in

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
    alias="meaningOfLife",
    args=[],
    instructions=[I32Const 42]
})) in
let useless = (Function({
    alias="useless",
    args=[],
    instructions=[I32Const 42, I32Const 23, I32Add()]
})) in
let add = (Function({
    alias="add",
    args=["lhs", "rhs"],
    instructions=[LocalGet "lhs", LocalGet "rhs", I32Add()]
})) in 
let m1 = Module({
    functions=[mol, useless],
    exports=["meaningOfLife", "useless"]
}) in

let m2 = Module({
    functions=[add],
    exports=["add"]
}) in

utest pprintInstr (I32Const 10) with "i32.const 10" in 
utest pprintInstr (I32Add()) with "i32.add" in 
utest pprintFunc mol with "(func $meaningOfLife (result i32) i32.const 42)" in
utest pprintFunc useless 
    with "(func $useless (result i32) i32.const 42\ni32.const 23\ni32.add)" in
utest pprintFunc add
    with "(func $add (param $lhs i32) (param $rhs i32) (result i32) local.get $lhs\nlocal.get $rhs\ni32.add)" in
(print (pprintMod m2))