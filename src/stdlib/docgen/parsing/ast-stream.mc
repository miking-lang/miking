include "map.mc"
include "mexpr/pprint.mc"

include "./utils.mc"
include "./sem-variants.mc"

include "../global/logger.mc"
include "../global/util.mc"
include "../global/objects.mc"

lang AstStreamInterface = Objects + MExprPrettyPrint

    type AstStreamContext = Expr 
    type LangDatabase = HashMap String Object


    type AstStreamNextResult = {
        -- ctx is the remaining AST to be processed after this item.
        ctx: AstStreamContext,
        name: String,
        info: Info,
        obj: Object
    }

    sem typeStreamHandleDecl : Decl -> AstStreamContext -> AstStreamNextResult

    sem typeStreamCreateLangDatabase : AstStreamContext -> String -> { database: LangDatabase, ctx: AstStreamContext }
    sem typeStreamCreateLangDatabase =
    | ctx -> lam. { database = hashmapEmpty (), ctx = ctx }

    sem getNextInfo : AstStreamContext -> Info
    sem getNextInfo =
    | TmDecl ({ info = info } & tm) -> info
    | _ -> NoInfo ()

    sem typeStreamNext : AstStreamContext -> Option AstStreamNextResult
    sem typeStreamNext =
    | TmDecl { decl = decl, inexpr = inexpr } -> Some (typeStreamHandleDecl decl inexpr)
    | _ -> None {}

    sem extractItemFailed =
    | ident -> lam langName.
        parsingWarn (join
         [ "Unable to parse item name from identifier `"
         , ident
         , "` using language `"
         , langName
         , "`."
         ])

end

lang ExternalAstStream = AstStreamInterface

  sem typeStreamHandleDecl =
  | DeclExt {ident = ident, tyIdent = tyIdent, info = info} ->
      lam ctx.
      let obj = ObjLet { ty = Some tyIdent, datas = objDefaultDatas () } in
      let info = concatInfos info (getNextInfo ctx) in
      { ctx = ctx, name = ident.0, info = info, obj = obj }

end

lang LetAstStream = AstStreamInterface

  sem typeStreamHandleDecl =
  | DeclLet { ident = ident, body = body, tyBody = tyBody, info = info } & decl ->
      lam ctx.
      let obj = ObjLet { ty = Some tyBody, datas = objDefaultDatas () } in
      let info = concatInfos info (getNextInfo ctx) in
      { ctx = ctx, name = ident.0, info = info, obj = obj }

end

lang TypeAstStream = AstStreamInterface

  sem getOptionalType : Type -> Option Type
  sem getOptionalType =
  | t -> if eqString "<>" (type2str t) then
         None {} else Some t

  sem typeStreamCreateLangDatabase =
  | TmDecl { decl = DeclType { tyIdent = tyIdent, ident = ident }, inexpr = inexpr } & ctx ->
      lam langName.
      let default = { database = hashmapEmpty (), ctx = ctx } in
      if not (belongToTheLang langName ident.0) then default else
      
      let obj =
          match getOptionalType tyIdent
          with Some t then ObjType { t = Some t, datas = objDefaultDatas () } 
          else ObjSyn { langName = langName, variants = [], datas = objDefaultDatas () }
      in

      match extractItemName langName ident.0
      with Some itemName then
          let res = typeStreamCreateLangDatabase inexpr langName in
          { res with database = hmInsert itemName obj res.database }
      else
          extractItemFailed ident.0 langName;
          default
      

  sem typeStreamHandleDecl =
  | DeclType { ident = ident, tyIdent = tyIdent, info = info } ->
      lam ctx.
      let t = getOptionalType tyIdent in
      let obj = ObjType { t = t, datas = objDefaultDatas () } in
      let info = concatInfos info (getNextInfo ctx) in      
      { ctx = ctx, name = ident.0, info = info, obj = obj }

end

lang ConAstStream = AstStreamInterface

  sem typeStreamCreateLangDatabase =
  | TmDecl { decl = DeclConDef { ident = ident, tyIdent = tyIdent }, inexpr = inexpr } & ctx ->
      lam langName.

      if not (belongToTheLang langName ident.0) then { database = hashmapEmpty (), ctx = ctx } else
    
      typeStreamCreateLangDatabase inexpr langName
      
  sem typeStreamHandleDecl =
  | DeclConDef { ident = ident, tyIdent = tyIdent, info = info } ->
      lam ctx.      
      let parentType = getParentType tyIdent in
      let obj = ObjCon { t = tyIdent, parentType = parentType , datas = objDefaultDatas () } in
      let info = concatInfos info (getNextInfo ctx) in      
      { ctx = ctx, name = ident.0, info = info, obj = obj }
end

lang UtestAstStream = AstStreamInterface

  sem typeStreamHandleDecl =
  | DeclUtest { info = info } ->
      lam ctx.      
      let obj = ObjUtest (objDefaultDatas ()) in
      let info = concatInfos info (getNextInfo ctx) in
      { ctx = ctx, name = "utest", info = info, obj = obj }
end

lang RecursiveAstStream = AstStreamInterface


  sem typeStreamCreateLangDatabase =
  | TmDecl { decl = DeclRecLets { bindings = bindings, info = info }, inexpr = inexpr } & ctx ->
      lam langName.
      let ident = tail (head bindings).ident.0 in -- sem name always start with a v, so we remove it.
      if not (belongToTheLang langName ident) then { database = hashmapEmpty (), ctx = ctx } else
      let database = foldl (
          lam acc. lam binding.
             let ident = binding.ident.0 in
             match extractItemName langName (tail ident)
             with Some itemName then
                 let variants = semVariantParse binding.body in
                 let obj = ObjSem { langName = langName, ty = Some binding.tyBody, datas = objDefaultDatas (), variants = variants } in
                 hmInsert itemName obj acc
             else
                 extractItemFailed ident langName;
                 acc
         ) (hashmapEmpty ()) bindings
      in
      { database = database, ctx = inexpr }
      


  sem typeStreamHandleDecl =
  | DeclRecLets { bindings = bindings, info = info } ->
      lam ctx.
      recursive let createDecl =
          lam bindings.
          match bindings with [binding] ++ bindings then
              let decl = DeclLet binding in
              TmDecl {
                  decl = decl,
                  inexpr = createDecl bindings,
                  info = infoDecl decl,
                  ty = binding.tyBody
              }
          else ctx
      in

      let ctx = createDecl bindings in
      optionGetOrElse
          (lam.
              parsingWarn "Failed to extract the first recursive binding (internal invariant violation).";
              let dummyObject = ObjUtest (objDefaultDatas ()) in
              { ctx = ctx, name = "", info = NoInfo (), obj = dummyObject })
          (typeStreamNext ctx)
end

lang AstStream =
    LetAstStream + TypeAstStream + ConAstStream + UtestAstStream + RecursiveAstStream + ExternalAstStream

    sem typeStreamFromExpr : Expr -> AstStreamContext 
    sem typeStreamFromExpr =
    | ast -> ast

    -- Builds a AstStream, creates an AST via the compiler's parser. Then types this AST via compiler's typer.
    -- Note that meta vars are not removed here    
    sem buildAstStream : MAst -> AstStreamContext
    sem buildAstStream = | ast ->
        typeStreamFromExpr ast
end
