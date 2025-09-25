-- # TypeStream Interface
-- 
-- This module defines the `TypeStreamInterface`, an API for managing type information traversal over a stack of MExpr expressions.  
-- Its main purpose is to simulate a stream-like behavior for typed `let`-bindings and to support recursive parsing of complex syntactic constructs such as `Lang` and `Sem`.
-- 
-- It exposes an abstract `TypeStreamContext` that maintains a stack of expressions, and two main operations:
-- 
-- - `typeStreamNext`: Iteratively searches for a `let`-binding matching a given name and returns its type and context, while skipping unrelated ones.
-- - `typeStreamPop`: Pops the top expression from the context stack, useful for recursively analyzing inner expressions.
--
-- This interface supports scenarios where expressions are not encountered in their declaration order, and enables deferred or conditional type lookups, crucial for features like `Lang` and `Sem` handling in Miking's semantics.
include "map.mc"

include "../global/logger.mc"
include "../global/util.mc"
    
lang TypeStreamInterface = MExprAst

    -- A context holding a stack of expressions yet to be processed.    
    type TypeStreamContext = { stack: [Expr] }

    -- The result of a typeStreamNext query.
    -- Includes:
    -- - The updated context
    -- - The optional type found
    -- - A list of skipped bindings that were not relevant to the query.
    type TypeStreamNextResult = { ctx: TypeStreamContext, t: Option Type, skipped: [{ name: String, body: Expr, t: Type }] }

    -- Searches the top of the context stack for a let-binding whose identifier matches the provided name.
    -- - If the top does not match, it is skipped and added to the skipped list.
    -- - If the stack is empty, returns None for the type and an unchanged context.        
    sem typeStreamNext : String -> TypeStreamContext -> TypeStreamNextResult
    sem typeStreamNext name =
    | { stack = [_] ++ stack } ->
        typeStreamNext name { stack = stack }
    | { stack = [] } & ctx -> { t = None {}, ctx = ctx, skipped = [] }

    -- Removes and returns the top expression (Expr) from the stack, updating the context accordingly.
    sem typeStreamPop : TypeStreamContext -> { ctx: TypeStreamContext, ast: Expr }
    sem typeStreamPop =
        | { stack = [ast] ++ stack } & ctx -> { ast = ast, ctx = { ctx with stack = stack }}

    -- Utility function that:
    -- - Immediately returns the type if the provided identifier matches the target name.
    -- - Otherwise, recursively invokes typeStreamNext, adding the current item to the skipped list.
    sem checkAndEnd name ident t body =
    | ctx -> if eqString name ident.0 then
            { t = Some t, ctx = ctx, skipped = [] }
        else  
            let res = typeStreamNext name ctx in
            { res with skipped = cons { name = ident.0, body = body, t = t } res.skipped }
end

lang AppTypeStream = TypeStreamInterface

  sem typeStreamNext name =
  | { stack = [TmApp { lhs = lhs, rhs = rhs }] ++ stack } ->

    typeStreamNext name { stack = concat [lhs, rhs] stack }

end


lang SeqTypeStream = TypeStreamInterface

  sem typeStreamNext name =
  | { stack = [TmSeq { tms = tms }] ++ stack } ->

    typeStreamNext name { stack = concat tms stack }

end


lang RecordTypeStream = TypeStreamInterface
    
    sem typeStreamNext name =
      | { stack = [TmRecord { bindings = bindings }] ++ stack } ->
        typeStreamNext name { stack = concat (mapValues  bindings) stack }
      | { stack = [TmRecordUpdate { rec = rec, value = value }] ++ stack } ->
        typeStreamNext name { stack = concat [rec, value] stack }

end


lang MatchTypeStream = TypeStreamInterface

  sem typeStreamNext name =
  | { stack = [TmMatch { target = target, thn = thn, els = els }] ++ stack } ->
    typeStreamNext name { stack = concat [target, thn, els] stack }
    
end

lang LamTypeStream = TypeStreamInterface

  sem typeStreamNext name =
  | { stack = [TmLam { body = body }] ++ stack } ->
    typeStreamNext name { stack = cons body stack }
    
end    

lang DeclTypeStream = TypeStreamInterface
    
  sem typeStreamNext name =
  | { stack = [TmDecl ({ decl = decl, inexpr = inexpr } & tm)] ++ stack } & ctx ->
            switch decl
            case DeclRecLets { bindings = [] } then
                typeStreamNext name { stack = cons inexpr stack }
            case DeclRecLets ({ bindings = [b] ++ bindings } & dl) then
                let ctx = { ctx with stack = concat [b.body, TmDecl { tm with decl = DeclRecLets { dl with bindings = bindings } } ] stack } in
                checkAndEnd name b.ident (b.tyBody) b.body ctx
            case DeclLet { ident = ident, body = body, tyBody = tyBody } then
                let ctx = { ctx with stack = concat [body, inexpr] stack } in
                checkAndEnd name ident tyBody body ctx
            case DeclUtest { test = test, expected = expected, tusing = tusing, tonfail = tonfail }  then
                let arr = [inexpr] in
                let arr = match tusing with Some tusing then cons tusing arr else arr in
                let arr = match tusing with Some tonfail then cons tonfail arr else arr in
                let arr = concat [test, expected] arr in
                typeStreamNext name { stack = concat arr stack }
            case _ then typeStreamNext name { ctx with stack = cons inexpr stack }
            end

end

lang TypeStream = DeclTypeStream + LamTypeStream + AppTypeStream + SeqTypeStream + RecordTypeStream + MatchTypeStream + MExprPrettyPrint
    sem typeStreamFromExpr : Expr -> TypeStreamContext 
    sem typeStreamFromExpr =
        | ast -> { stack = [ast] }

    -- Builds a TypeStream, creates an AST via the compiler's parser. Then types this AST via compiler's typer.
    -- Note that meta vars are not removed here    
    sem buildTypeStream : MAst -> TypeStreamContext
    sem buildTypeStream = | ast -> typeStreamFromExpr ast.expr
end 
    
