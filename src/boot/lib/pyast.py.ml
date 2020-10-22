type 'a ext =
  | PyObject of Py.Object.t
  | Pyimport
  | Pycall of Py.Object.t option * string option
  | PycallKw of Py.Object.t option * string option * Py.Object.t Array.t option
  | Pyconvert
