// String format with MLang

include "char.mc"
include "seq.mc"
include "string.mc"

lang FmtInteger
	syn Fmt =
	| FmtInt (Int)

	sem toString =
	| FmtInt n -> int2string n
end

lang FmtFloat
	syn Fmt =
	| FmtFloat (Float)

	sem toString =
	| FmtFloat f -> float2string f
end

lang FmtString
	syn Fmt =
	| FmtStr (String)

	sem toString =
	| FmtStr s -> s
end

lang FmtChar
	syn Fmt =
	| FmtChar (Char)

	sem toString =
	| FmtChar c -> [c]
end

lang StrFormatBase
	syn Fmt =
	-- Intentionally left blank

	sem toString =
	| _ -> error "StrFormatBase: toString: Unknown Fmt"

	sem strFormat (args : [Fmt]) =
	| s ->
		if lti (length s) 2 then
			s
		else if eqchar '%' (head s) then
			let c = head (tail s) in
			if eqchar '%' c then
				cons '%' (strFormat args (tail (tail s)))
			else if is_alpha c then
				-- At the moment just accept any alpha char to represent a format
				concat (toString (head args)) (strFormat (tail args) (tail (tail s)))
			else
				error "StrFormatBase: strFormat: Unrecognized format"
		else
			cons (head s) (strFormat args (tail s))
end


lang StandardFormats = FmtInteger + FmtFloat + FmtString + FmtChar

lang StrFormat = StandardFormats + StrFormatBase

mexpr

use StrFormat in
let sprintf = lam s. lam args. strFormat args s in
let printf = lam s. lam args. print (sprintf s args) in

utest sprintf "%d + %d = %d" [FmtInt(2), FmtInt(3), FmtInt(addi 2 3)] with "2 + 3 = 5" in
utest sprintf "Give it %T%%" [FmtInt(101)] with "Give it 101%" in
utest sprintf "Hello, %s!" [FmtStr("John Doe")] with "Hello, John Doe!" in
utest sprintf "My initials are %c.%c." [FmtChar('J'), FmtChar('D')] with "My initials are J.D." in
utest sprintf "%a means %a" [FmtStr("Five"), FmtInt(5)] with "Five means 5" in

()
