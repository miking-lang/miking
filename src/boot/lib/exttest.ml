type myrec1_t = {a: int; b: float}

type myrec2_t = {a: int list; b: int}

let list_of_lists = [[0]]

let list_hd_hd ls = ls |> List.hd |> List.hd

let array_of_arrays = [|[|0|]|]

let array_hd_hd a = a.(0).(0)

let arg_label ~a ~b = b - a

let tuple1 = (1, 2.)

let tuple2 = ([1], 2)

let tuple1_0th (x, _) = x + 1

let tuple2_0th (x, _) = List.map (( + ) 1) x

let myrec1 : myrec1_t = {a= 1; b= 2.}

let myrec1_a (r : myrec1_t) = r.a + 1

let myrec2 : myrec2_t = {a= [1]; b= 2}

let myrec2_a (r : myrec2_t) = List.map (( + ) 1) r.a
