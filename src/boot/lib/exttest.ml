type myrec1_t = {a: int; b: float}

type myrec2_t = {b: int; a: int list}

type myrec3_t = {a: myrec1_t; b: myrec2_t}

let list_of_lists = [[0]]

let list_hd_hd ls = ls |> List.hd |> List.hd

let array_of_arrays = [|[|0|]|]

let array_hd_hd a = a.(0).(0)

let arg_label ~a ~b = b - a

let unit1 x =
  let _ = x + 1 in
  ()

let unit2 = function () -> 1

let tuple1 = (1, 3.)

let tuple2 = ([1], 2)

let tuple1_0th (x, _) = x + 1

let tuple2_0th (x, _) = List.map (( + ) 1) x

let myrec1 : myrec1_t = {a= 1; b= 3.}

let myrec1_a (r : myrec1_t) = r.a + 1

let myrec2 : myrec2_t = {b= 2; a= [1]}

let myrec2_a (r : myrec2_t) = List.map (( + ) 1) r.a

let myrec3 : myrec3_t = {a= myrec1; b= myrec2}

let myrec3_b_a (r : myrec3_t) = List.map (( + ) 1) r.b.a
