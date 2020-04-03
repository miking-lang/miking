// String format with MLang

include "char.mc"
include "seq.mc"
include "string.mc"

lang FormatInteger
  syn Fmt =
  | FmtInt (Int)

  sem toString =
  | FmtInt n -> int2string n

  sem toFormat (fmtstr : String) =
  | FmtInt n ->
    if eqstr fmtstr "%d" then
      int2string n
    else
      error (concat "FormatInteger: toFormat: Unrecognized format: " fmtstr)
end

lang FormatFloat
  syn Fmt =
  | FmtFloat (Float)

  sem toString =
  | FmtFloat f -> float2string f

  sem toFormat (fmtstr : String) =
  | FmtFloat f ->
    if eqstr fmtstr "%f" then
      float2string f
    else
      error (concat "FormatFloat: toFormat: Unrecognized format: " fmtstr)
end

lang FormatString
  syn Fmt =
  | FmtStr (String)

  sem toString =
  | FmtStr s -> s

  sem toFormat (fmtstr : String) =
  | FmtStr s ->
    if eqstr fmtstr "%s" then
      s
    else if eqstr fmtstr "%^s" then
      str2upper s
    else if eqstr fmtstr "%_s" then
      str2lower s
    else
      error (concat "FormatString: toFormat: Unrecognized format: " fmtstr)
end

lang FormatChar
  syn Fmt =
  | FmtChar (Char)

  sem toString =
  | FmtChar c -> [c]

  sem toFormat (fmtstr : String) =
  | FmtChar c ->
    if eqstr fmtstr "%c" then
      [c]
    else
      error (concat "FormatChar: toFormat: Unrecognized format: " fmtstr)
end

lang StrFormatBase
  syn Fmt =
  -- Intentionally left blank

  sem toString =
  | _ -> error "StrFormatBase: toString: Unknown Fmt"

  sem toFormat (fmtstr : String) =
  | _ -> error "StrFormatBase: toFormat: Unknown Fmt"

  sem strFormat (args : [Fmt]) =
  | s ->
    if lti (length s) 2 then
      s
    else if eqchar '%' (head s) then
      let c = head (tail s) in
      if eqchar '%' c then
        cons '%' (strFormat args (tail (tail s)))
      else if eqchar c '*' then
        -- %* represents a wildcard format; The argument is converted
        -- to _some_ string.
        concat (toString (head args)) (strFormat (tail args) (tail (tail s)))
      else
        -- A valid format: %(...)X
        -- Where X represents any alpha char and (...) represents any
        -- sequence of non-alpha chars.
        let found_idx = index is_alpha s in
        match found_idx with Some i then
          let fmtstr = slice s 0 (addi i 1) in
          let remaining = slice s (addi i 1) (length s) in
          concat (toFormat fmtstr (head args)) (strFormat (tail args) remaining)
        else
          error (concat "StrFormatBase: strFormat: Unrecognized format: " s)
    else
      cons (head s) (strFormat args (tail s))
end


lang StandardFormats = FormatInteger + FormatFloat + FormatString + FormatChar

lang StrFormat = StandardFormats + StrFormatBase

mexpr

use StrFormat in
let sprintf = lam s. lam args. strFormat args s in
let printf = lam s. lam args. print (sprintf s args) in

utest sprintf "%d + %d = %d" [FmtInt(2), FmtInt(3), FmtInt(addi 2 3)] with "2 + 3 = 5" in
utest sprintf "Give it %d%%" [FmtInt(101)] with "Give it 101%" in
utest sprintf "Hello, %s!" [FmtStr("John Doe")] with "Hello, John Doe!" in
utest sprintf "My initials are %c.%c." [FmtChar('J'), FmtChar('D')] with "My initials are J.D." in
utest sprintf "%* means %*" [FmtStr("Five"), FmtInt(5)] with "Five means 5" in

utest sprintf "%s should be %_s or %^s" (makeSeq 3 (FmtStr ("cAsE"))) with "cAsE should be case or CASE" in

()
