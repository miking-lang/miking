// String format with MLang

include "char.mc"
include "seq.mc"
include "string.mc"

lang TypeInteger
	syn Type =
	| TyInt (Int)

	sem toString =
	| TyInt v -> int2string v
end

lang TypeFloat
	syn Type =
	| TyFloat (Float)

	sem toString =
	| TyFloat v -> float2string v
end

lang StrFormatBase
	syn Type =

	syn Operand =
	| CStrFormat (String)

	sem toString =
	| _ -> error "StrFormatBase: toString: Unknown type"

	sem eval (args : [Type]) =
	| CStrFormat s ->
		if lti (length s) 2 then
			s 
		else if eqchar '%' (head s) then
			let c = head (tail s) in
			if eqchar '%' c then
				cons '%' (eval args (CStrFormat (tail (tail s))))
			else if is_alpha c then
				-- At the moment just accept any alpha char to represent a format
				concat (toString (head args)) (eval (tail args) (CStrFormat (tail (tail s))))
			else
				error "StrFormatBase: eval: Unrecognized format"
		else
			cons (head s) (eval args (CStrFormat (tail s)))
end

lang StrFormat = StrFormatBase + TypeInteger + TypeFloat

mexpr

use StrFormat in
let sprintf = lam s. lam args. eval args (CStrFormat (s)) in
let printf = lam s. lam args. print (sprintf s args) in

utest sprintf "%d + %d = %d" [TyInt(2), TyInt(3), TyInt(addi 2 3)] with "2 + 3 = 5" in
utest sprintf "Give it %T%%" [TyInt(101)] with "Give it 101%" in

printf "\n >Test Print:\n >%a/%a = %a\n" [TyInt(10), TyInt(3), TyFloat(divf (int2float 10) (int2float 3))]
