include "map.mc"

include "mexpr/ast.mc"

include "mlang/ast.mc"

include "extrec/ast.mc"

type CosemTyAnnotContext = {
  baseMap : Map Name Name,
  tyAnnotMap : Map Name (use Ast in Type)
}

lang CosemTyAnnot = MLangAst 
  sem handleCosemTyAnnot : Map Name Name -> MLangProgram -> MLangProgram
  sem handleCosemTyAnnot baseMap = 
  | prog ->
    printLn (int2string (length prog.decls));

    let ctx = { baseMap = baseMap, tyAnnotMap = mapEmpty nameCmp} in
    match mapAccumL handleCosemTyAnnot_Decl ctx prog.decls 
    with (_, decls) in 

    printLn (int2string (length decls));

    {prog with decls = decls}

  sem handleCosemTyAnnot_Decl : CosemTyAnnotContext -> Decl -> (CosemTyAnnotContext, Decl)
  sem handleCosemTyAnnot_Decl ctx = 
  | decl & DeclCosem d -> 
    printLn "Here!";
    if d.isBase then 
      ({ctx with tyAnnotMap = mapInsert d.ident d.tyAnnot ctx.tyAnnotMap}, decl)
    else
      match mapLookup d.ident ctx.baseMap with Some baseIdent in 
      let tyAnnot = match mapLookup baseIdent ctx.tyAnnotMap 
                    with Some tyAnnot then tyAnnot
                    else errorSingle [d.info] (join [
                      "* The cosem ", (nameGetStr d.ident), " is not a base cosem and does ",
                      "not have a type annotation!\n",
                      "* Please provide a type annotation for the cosem at the",
                      " base declaration."
                    ]) in 
       (ctx, DeclCosem {d with tyAnnot = tyAnnot})
  | d -> 
    smapAccumL_Decl_Decl handleCosemTyAnnot_Decl ctx d
end