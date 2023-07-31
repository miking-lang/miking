-- TODO Comment describing the functionality in the file

include "ast.mc"
include "eq.mc"

include "json.mc"

-- NOTE Use stdlib.mc (and stdlibLoc in particular) to load json.mc and combine with input expr.

lang GenerateJsonSerializers = Ast

  sem generateJsonSerializers: Set Type -> Expr -> (Map Type (Name,Name) -> Expr)

end
