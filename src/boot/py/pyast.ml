type 'a ext =
| PyObject of Py.Object.t
| Pyimport
| Pycall of Py.Object.t option * string option
