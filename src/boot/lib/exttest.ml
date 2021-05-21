let list_of_lists = [[0]]

let list_hd_hd ls = ls |> List.hd |> List.hd

let array_of_arrays = [|[|0|]|]

let array_hd_hd a = a.(0).(0)

let arg_label ~a:a ~b:b = b - a

let tuple1 = (1, 2.)

let tuple2 = ([1], 2)

let tuple_0th1 (x, _) = x + 1

let tuple_0th2 (x, _) = List.map (( + ) 1) x
