lang RowHelpers = ExtRecordType + MetaVarTypeAst +
                  MExprPrettyPrint
  sem _deplookup : ExtRecEnvType -> Name -> Set Name
  sem _deplookup env = 
  | name ->
    match mapLookup name env.tyDeps with Some deps in 
    deps

  sem _labeldep_lookup : ExtRecEnvType -> Name -> String -> Set Name
  sem _labeldep_lookup env n =
  | label ->
    match mapLookup n env.labelTyDeps with Some innerMap in 
    match mapLookup label innerMap with Some deps in 
    deps

  sem _labelseq : ExtRecEnvType -> Name -> [String]
  sem _labelseq env =
  | name ->
    match mapLookup name env.defs with Some labelToType in 
    mapKeys labelToType

  sem _update_row : String -> Type -> Type -> Type
  sem _update_row label pre =
  | ExtRecordRow t ->
    ExtRecordRow {t with row = mapInsert label pre t.row}

  sem _get_row : Name -> Type -> Type 
  sem _get_row name = 
  | TyMapping {mapping = m} -> 
    match mapLookup name m with Some row then
      row
    else
      error (join [
        "The provided name '",
        nameGetStr name,
        "' does not occur in the mapping!"
      ])

  sem _update_mapping : Name -> Type -> Type -> Type 
  sem _update_mapping name row = 
  | TyMapping t ->
    TyMapping {t with mapping = mapInsert name row t.mapping}

  sem _update_row_mapping : Name -> String -> Type -> Type -> Type
  sem _update_row_mapping name label pre =
  | ty -> 
    _update_mapping name (_update_row label pre (_get_row name ty)) ty

  sem _restrict_mapping : Set Name -> Type -> Type
  sem _restrict_mapping tydeps = 
  | TyMapping t -> 
    let mappingKeySet = setOfKeys t.mapping in

    -- Ensure that the provided mapping domain contains all tydeps
    (if not (setSubset tydeps mappingKeySet) then
       error "Incomplete mapping!"
     else 
       ());

    let work = lam acc. lam n. lam row.
      if setMem n tydeps then
        mapInsert n row acc 
      else 
        acc
    in 

    let mapping = mapFoldWithKey work (mapEmpty nameCmp) t.mapping in
    TyMapping {t with mapping = mapping}

  sem completePolyMapping : TCEnv -> Name -> Type
  sem completePolyMapping env =
  | name ->
    let deps = _deplookup env.extRecordType name in 

    let dep2row = lam n. 
      let labels = _labelseq env.extRecordType n in 
      let label2pair = lam label. (label, newnmetavar (concat "theta_" label) (Presence ()) env.currentLvl (NoInfo ())) in 
      let pairs = map label2pair labels in 
      ExtRecordRow {ident = n, 
                    row = mapFromSeq cmpString pairs} 
    in 

    let mappingPairs = map (lam dep. (dep, dep2row dep)) (setToSeq deps) in 
    TyMapping {mapping = mapFromSeq nameCmp mappingPairs}
end