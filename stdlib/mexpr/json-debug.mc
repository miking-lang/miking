-- This file supplies a set of functions for dumping MExpr ASTs to
-- json, which can then be printed and examined in various other tools
-- for exploring json values.

include "json.mc"
include "mexpr/pprint.mc"
include "mexpr/ast.mc"
include "mexpr/type.mc"
include "mlang/ast.mc"

lang AstToJson = Ast + DeclAst
  sem exprToJson : Expr -> JsonValue
  sem typeToJson : Type -> JsonValue
  sem kindToJson : Kind -> JsonValue
  sem patToJson : Pat -> JsonValue
  sem declToJson : Decl -> JsonValue

  sem optToNull : Option JsonValue -> JsonValue
  sem optToNull =
  | Some x -> x
  | None _ -> JsonNull ()

  sem nameToJson : Name -> JsonValue
  sem nameToJson = | name ->
    JsonArray [JsonString (nameGetStr name), optToNull (optionMap (lam x. JsonInt (sym2hash x)) (nameGetSym name))]

  sem patNameToJson : PatName -> JsonValue
  sem patNameToJson =
  | PName n -> nameToJson n
  | PWildcard _ -> JsonString "_"

  sem infoToJson : Info -> JsonValue
  sem infoToJson = | info -> JsonString (info2str info)

  -- TODO(vipa, 2024-05-16): This is a temporary helper until
  -- https://github.com/miking-lang/miking/issues/826 is implemented
  sem exprAsDecl : Expr -> Option (Decl, Expr)
  sem exprAsDecl =
  | _ -> None ()
end

lang VarToJson = AstToJson + VarAst
  sem exprToJson =
  | TmVar x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmVar")
    , ("ident", nameToJson x.ident)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    , ("frozen", JsonBool x.frozen)
    ] )
end

lang AppToJson = AstToJson + AppAst
  sem exprToJson =
  | TmApp x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmApp")
    , ("lhs", exprToJson x.lhs)
    , ("rhs", exprToJson x.rhs)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang LamToJson = AstToJson + LamAst
  sem exprToJson =
  | TmLam x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmLam")
    , ("ident", nameToJson x.ident)
    , ("tyAnnot", typeToJson x.tyAnnot)
    , ("tyParam", typeToJson x.tyParam)
    , ("body", exprToJson x.body)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang DeclsToJson = AstToJson + LetAst + LetDeclAst + RecLetsAst + RecLetsDeclAst + TypeAst + TypeDeclAst + DataAst + DataDeclAst + UtestAst + UtestDeclAst + ExtAst + ExtDeclAst
  sem exprAsDecl =
  | TmLet x -> Some
    ( DeclLet {ident = x.ident, tyAnnot = x.tyAnnot, tyBody = x.tyBody, body = x.body, info = x.info}
    , x.inexpr
    )
  | TmRecLets x -> Some
    ( DeclRecLets {info = x.info, bindings = x.bindings}
    , x.inexpr
    )
  | TmType x -> Some
    ( DeclType {ident = x.ident, params = x.params, tyIdent = x.tyIdent, info = x.info}
    , x.inexpr
    )
  | TmConDef x -> Some
    ( DeclConDef {ident = x.ident, tyIdent = x.tyIdent, info = x.info}
    , x.inexpr
    )
  | TmUtest x -> Some
    ( DeclUtest {test = x.test, expected = x.expected, tusing = x.tusing, tonfail = x.tonfail, info = x.info}
    , x.next
    )
  | TmExt x -> Some
    ( DeclExt {ident = x.ident, tyIdent = x.tyIdent, effect = x.effect, info = x.info}
    , x.inexpr
    )

  sem exprToJson =
  | tm & (TmLet _ | TmRecLets _ | TmType _ | TmConDef _ | TmUtest _ | TmExt _) ->
    recursive let work = lam acc. lam expr.
      match exprAsDecl expr with Some (decl, inexpr) then
        work (snoc acc decl) inexpr
      else (acc, expr) in
    match work [] tm with (decls, inexpr) in
    JsonObject (mapFromSeq cmpString
      [ ("con", JsonString "TmDecl (merged)")
      , ("decls", JsonArray (map declToJson decls))
      , ("inexpr", exprToJson inexpr)
      , ("ty", typeToJson (tyTm tm))
      , ("info", infoToJson (infoTm tm))
      ] )
end

lang ConstToJson = AstToJson + ConstAst + ConstPrettyPrint
  sem exprToJson =
  | TmConst x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmConst")
    , ("const", JsonString (getConstStringCode 0 x.val))
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang SeqToJson = AstToJson + SeqAst
  sem exprToJson =
  | TmSeq x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmSeq")
    , ("tms", JsonArray (map exprToJson x.tms))
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang RecordToJson = AstToJson + RecordAst
  sem exprToJson =
  | TmRecord x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmRecord")
    , ("bindings", JsonObject
      (mapFromSeq cmpString
        (map (lam x. (sidToString x.0, exprToJson x.1))
          (mapBindings x.bindings))))
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
  | TmRecordUpdate x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmRecordUpdate")
    , ("rec", exprToJson x.rec)
    , ("key", JsonString (sidToString x.key))
    , ("value", exprToJson x.value)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang ConAppToJson = AstToJson + DataAst
  sem exprToJson =
  | TmConApp x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmConApp")
    , ("ident", nameToJson x.ident)
    , ("body", exprToJson x.body)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang MatchToJson = AstToJson + MatchAst
  sem exprToJson =
  | TmMatch x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmMatch")
    , ("target", exprToJson x.target)
    , ("pat", patToJson x.pat)
    , ("thn", exprToJson x.thn)
    , ("els", exprToJson x.els)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang NeverToJson = AstToJson + NeverAst
  sem exprToJson =
  | TmNever x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmNever")
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang NamedPatToJson = AstToJson + NamedPat
  sem patToJson =
  | PatNamed x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatNamed")
    , ("ident", patNameToJson x.ident)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang SeqTotPatToJson = AstToJson + SeqTotPat
  sem patToJson =
  | PatSeqTot x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatSeqTot")
    , ("pats", JsonArray (map patToJson x.pats))
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang SeqEdgePatToJson = AstToJson + SeqEdgePat
  sem patToJson =
  | PatSeqEdge x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatSeqEdge")
    , ("prefix", JsonArray (map patToJson x.prefix))
    , ("middle", patNameToJson x.middle)
    , ("postfix", JsonArray (map patToJson x.postfix))
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang RecordPatToJson = AstToJson + RecordPat
  sem patToJson =
  | PatRecord x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatRecord")
    , ("bindings", JsonObject
      (mapFromSeq cmpString
        (map (lam x. (sidToString x.0, patToJson x.1))
          (mapBindings x.bindings))))
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang DataPatToJson = AstToJson + DataPat
  sem patToJson =
  | PatCon x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatCon")
    , ("ident", nameToJson x.ident)
    , ("subpat", patToJson x.subpat)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang IntPatToJson = AstToJson + IntPat
  sem patToJson =
  | PatInt x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatInt")
    , ("val", JsonInt x.val)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang CharPatToJson = AstToJson + CharPat
  sem patToJson =
  | PatChar x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatChar")
    , ("val", JsonString [x.val])
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang BoolPatToJson = AstToJson + BoolPat
  sem patToJson =
  | PatBool x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatBool")
    , ("val", JsonBool x.val)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang AndPatToJson = AstToJson + AndPat
  sem patToJson =
  | PatAnd x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatAnd")
    , ("lpat", patToJson x.lpat)
    , ("rpat", patToJson x.rpat)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang OrPatToJson = AstToJson + OrPat
  sem patToJson =
  | PatOr x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatOr")
    , ("lpat", patToJson x.lpat)
    , ("rpat", patToJson x.rpat)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang NotPatToJson = AstToJson + NotPat
  sem patToJson =
  | PatNot x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "PatNot")
    , ("subpat", patToJson x.subpat)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang UnknownTypeToJson = AstToJson + UnknownTypeAst
  sem typeToJson =
  | TyUnknown x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyUnknown")
    , ("info", infoToJson x.info)
    ] )
end

lang BoolTypeToJson = AstToJson + BoolTypeAst
  sem typeToJson =
  | TyBool x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyBool")
    , ("info", infoToJson x.info)
    ] )
end

lang IntTypeToJson = AstToJson + IntTypeAst
  sem typeToJson =
  | TyInt x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyInt")
    , ("info", infoToJson x.info)
    ] )
end

lang FloatTypeToJson = AstToJson + FloatTypeAst
  sem typeToJson =
  | TyFloat x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyFloat")
    , ("info", infoToJson x.info)
    ] )
end

lang CharTypeToJson = AstToJson + CharTypeAst
  sem typeToJson =
  | TyChar x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyChar")
    , ("info", infoToJson x.info)
    ] )
end

lang FunTypeToJson = AstToJson + FunTypeAst
  sem typeToJson =
  | TyArrow x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyArrow")
    , ("from", typeToJson x.from)
    , ("to", typeToJson x.to)
    , ("info", infoToJson x.info)
    ] )
end

lang SeqTypeToJson = AstToJson + SeqTypeAst
  sem typeToJson =
  | TySeq x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TySeq")
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang TensorTypeToJson = AstToJson + TensorTypeAst
  sem typeToJson =
  | TyTensor x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyTensor")
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang RecordTypeToJson = AstToJson + RecordTypeAst
  sem typeToJson =
  | TyRecord x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyRecord")
    , ("fields", JsonObject
      (mapFromSeq cmpString
        (map (lam x. (sidToString x.0, typeToJson x.1))
          (mapBindings x.fields))))
    , ("info", infoToJson x.info)
    ] )
end

lang VariantTypeToJson = AstToJson + VariantTypeAst
  sem typeToJson =
  | TyVariant x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyVariant")
    , ("constrs", JsonArray
      (map (lam x. JsonArray [nameToJson x.0, typeToJson x.1])
        (mapBindings x.constrs)))
    , ("info", infoToJson x.info)
    ] )
end

lang ConTypeToJson = AstToJson + ConTypeAst
  sem typeToJson =
  | TyCon x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyCon")
    , ("ident", nameToJson x.ident)
    , ("data", typeToJson x.data)
    , ("info", infoToJson x.info)
    ] )
end

lang DataTypeToJson = AstToJson + DataTypeAst
  sem typeToJson =
  | TyData x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyData")
    , ("universe", JsonArray
      (map (lam x. JsonArray [nameToJson x.0, JsonArray (map nameToJson (setToSeq x.1))])
        (mapBindings x.universe)))
    , ("positive", JsonBool x.positive)
    , ("cons", JsonArray (map nameToJson (setToSeq x.cons)))
    , ("info", infoToJson x.info)
    ] )
end

lang VarTypeToJson = AstToJson + VarTypeAst
  sem typeToJson =
  | TyVar x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyVar")
    , ("ident", nameToJson x.ident)
    , ("info", infoToJson x.info)
    ] )
end

lang AllTypeToJson = AstToJson + AllTypeAst
  sem typeToJson =
  | TyAll x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyAll")
    , ("ident", nameToJson x.ident)
    , ("kind", kindToJson x.kind)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang AppTypeToJson = AstToJson + AppTypeAst
  sem typeToJson =
  | TyApp x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyApp")
    , ("lhs", typeToJson x.lhs)
    , ("rhs", typeToJson x.rhs)
    , ("info", infoToJson x.info)
    ] )
end

lang AliasTypeToJson = AstToJson + AliasTypeAst
  sem typeToJson =
  | TyAlias x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyAlias")
    , ("display", typeToJson x.display)
    , ("content", typeToJson x.content)
    ] )
end

lang PolyKindToJson = AstToJson + PolyKindAst
  sem kindToJson =
  | Poly _ -> JsonString "Poly"
end

lang MonoKindToJson = AstToJson + MonoKindAst
  sem kindToJson =
  | Mono _ -> JsonString "Mono"
end

lang RecordKindToJson = AstToJson + RecordKindAst
  sem kindToJson =
  | Record x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "Record")
    , ("bindings", JsonObject
      (mapFromSeq cmpString
        (map (lam x. (sidToString x.0, typeToJson x.1))
          (mapBindings x.fields))))
    ] )
end

lang DataKindToJson = AstToJson + DataKindAst
  sem kindToJson =
  | Data x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "Data")
    , ("types",
      let inner = lam r. JsonObject (mapFromSeq cmpString
        [ ("lower", JsonArray (map nameToJson (setToSeq r.lower)))
        , ("upper", optToNull
          (optionMap (lam upper. JsonArray (map nameToJson (setToSeq upper)))
            r.upper))
        ] ) in
      JsonArray (map (lam x. JsonArray [nameToJson x.0, inner x.1])
        (mapBindings x.types)))
    ] )
end

lang UseToJson = AstToJson + UseAst
  -- TODO(vipa, 2024-05-17): This should probably actually be a Decl,
  -- it's just not a good idea to do a `use` on the top-level right
  -- now because of how includes work.
  sem exprToJson =
  | TmUse x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmUse")
    , ("ident", nameToJson x.ident)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
end

lang LetToJson = LetDeclAst + AstToJson
  sem declToJson =
  | DeclLet x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "DeclLet")
    , ("ident", nameToJson x.ident)
    , ("tyAnnot", typeToJson x.tyAnnot)
    , ("tyBody", typeToJson x.tyBody)
    , ("body", exprToJson x.body)
    , ("info", infoToJson x.info)
    ] )
end

-- DeclType --
lang TypeToJson = TypeDeclAst + AstToJson
  sem declToJson =
  | DeclType x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "DeclType")
    , ("ident", nameToJson x.ident)
    , ("params", JsonArray (map nameToJson x.params))
    , ("tyIdent", typeToJson x.tyIdent)
    , ("info", infoToJson x.info)
    ] )
end

-- DeclRecLets --
lang RecLetsToJson = RecLetsDeclAst + RecLetsAst + AstToJson
  sem declToJson =
  | DeclRecLets x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "DeclRecLets")
    , ( "bindings"
      , let bindingToJson = lam b. JsonObject (mapFromSeq cmpString
          [ ("ident", nameToJson b.ident)
          , ("tyAnnot", typeToJson b.tyAnnot)
          , ("tyBody", typeToJson b.tyBody)
          , ("body", exprToJson b.body)
          , ("info", infoToJson b.info)
          ] ) in
        JsonArray (map bindingToJson x.bindings)
      )
    , ("info", infoToJson x.info)
    ] )
end

-- DeclConDef --
lang DataToJson = DataDeclAst + AstToJson
  sem declToJson =
  | DeclConDef x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "DeclConDef")
    , ("ident", nameToJson x.ident)
    , ("tyIdent", typeToJson x.tyIdent)
    , ("info", infoToJson x.info)
    ] )
end

-- DeclUtest --
lang UtestToJson = UtestDeclAst + AstToJson
  sem declToJson =
  | DeclUtest x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "DeclUtest")
    , ("test", exprToJson x.test)
    , ("expected", exprToJson x.expected)
    , ("tusing", optToNull (optionMap exprToJson x.tusing))
    , ("info", infoToJson x.info)
    ] )
end

-- DeclExt --
lang ExtToJson = ExtDeclAst + AstToJson
  sem declToJson =
  | DeclExt x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "DeclExt")
    , ("ident", nameToJson x.ident)
    , ("tyIdent", typeToJson x.tyIdent)
    , ("effect", JsonBool x.effect)
    , ("info", infoToJson x.info)
    ] )
end

lang MetaVarToJson = AstToJson + MetaVarTypeAst
  sem typeToJson =
  | TyMetaVar x ->
    let contents = switch deref x.contents
      case Unbound u then
        JsonObject (mapFromSeq cmpString
          [ ("ident", nameToJson u.ident)
          , ("level", JsonInt u.level)
          , ("kind", kindToJson u.kind)
          ])
      case Link ty then
        typeToJson ty
      end in
    JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyMetaVar")
    , ("contents", contents)
    ] )
end

lang MExprToJson
  = VarToJson
  + AppToJson
  + LamToJson
  + DeclsToJson
  + ConstToJson
  + SeqToJson
  + RecordToJson
  + ConAppToJson
  + MatchToJson
  + NeverToJson
  + NamedPatToJson
  + SeqTotPatToJson
  + SeqEdgePatToJson
  + RecordPatToJson
  + DataPatToJson
  + IntPatToJson
  + CharPatToJson
  + BoolPatToJson
  + AndPatToJson
  + OrPatToJson
  + NotPatToJson
  + UnknownTypeToJson
  + BoolTypeToJson
  + IntTypeToJson
  + FloatTypeToJson
  + CharTypeToJson
  + FunTypeToJson
  + SeqTypeToJson
  + TensorTypeToJson
  + RecordTypeToJson
  + VariantTypeToJson
  + ConTypeToJson
  + DataTypeToJson
  + VarTypeToJson
  + AllTypeToJson
  + AppTypeToJson
  + AliasTypeToJson
  + PolyKindToJson
  + MonoKindToJson
  + RecordKindToJson
  + DataKindToJson
  + UseToJson
  + LetToJson
  + TypeToJson
  + RecLetsToJson
  + DataToJson
  + UtestToJson
  + ExtToJson
  + MetaVarToJson
end

mexpr

use MExprToJson in

utest json2string (exprToJson unit_) with "{\"ty\":{\"con\":\"TyRecord\",\"info\":\"<No file info>\",\"fields\":{}},\"con\":\"TmRecord\",\"info\":\"<No file info>\",\"bindings\":{}}" in

()
