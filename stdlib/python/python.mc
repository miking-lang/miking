let _blt = pyimport "builtins"

let pythonGetAttr = lam pyobj. lam attr.
  pycall _blt "getattr" (pyobj, attr)
