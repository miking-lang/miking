include "name.mc"
include "mexpr/info.mc"

-- Defines simple convenience functions for name-info tuples.

let _eqn = lam n1. lam n2.
  if and (nameHasSym n1) (nameHasSym n2) then
    nameEqSym n1 n2
  else
    error "Name without symbol."

type NameInfo = (Name, Info)

let nameInfoCmp = lam v1 : NameInfo. lam v2 : NameInfo.
  nameCmp v1.0 v2.0

let nameInfoEq = lam l1 : NameInfo. lam l2 : NameInfo.
  _eqn l1.0 l2.0

let nameInfoGetStr = lam ni : NameInfo.
  nameGetStr ni.0

let nameInfoGetName = lam ni : NameInfo.
  ni.0

let nameInfoGetInfo = lam ni : NameInfo.
  ni.1
