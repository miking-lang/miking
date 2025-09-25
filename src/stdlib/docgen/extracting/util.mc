-- # Path and Syntax Utilities
-- This module provides a collection of utility functions used for: path manipulation and syntax tree processing, many functions operate on `DocTree` nodes
-- These functions are essentialy used in the extracting.mc file.

include "../parsing/doc-tree.mc"
include "../parsing/lexing/token-readers.mc"
include "../global/util.mc"
include "string.mc"
include "stdlib.mc"
include "sys.mc"
include "../global/logger.mc"

-- Compute the namespace of an object based on path name and ext.
let getNamespace = lam path. lam name. lam ext.
    let ext = match ext with "" then "" else concat ext "-" in
    join [path, "/", ext, name]


-- Extracts the last segment of a namespace (split by '/').
-- Example: extractLastNamespaceElement "foo/bar/baz" returns "baz"
let extractLastNamespaceElement = lam namespace.
    let namespace = match strSplit "/" namespace with ([_] ++ _) & namespace then head (reverse namespace) else "" in
    match strSplit "-" namespace with ([_] ++ _) & namespace then head (reverse namespace) else namespace

utest extractLastNamespaceElement "a/b/c" with "c"
utest extractLastNamespaceElement "onlyone" with "onlyone"
utest extractLastNamespaceElement "" with ""


-- Removes all comment tokens from a list of syntax tree nodes.
let removeComments : [DocTree] -> [DocTree] = use TokenReader in
    lam sons. filter (lam s. match s with DocTreeLeaf { token = TokenComment {} } then false else true) sons

-- Returns the nth word in the list of syntax tree nodes.
-- Ignores non-word tokens.
recursive let nthWord = use TokenReader in lam sons. lam n.
    switch sons
    case [DocTreeLeaf { token = (TokenWord { content = word } | TokenStr { content = word }) }] ++ rest then
        if eqi n 0 then Some { word = word, rest = rest }
        else nthWord rest (subi n 1)
    case [_] ++ rest then nthWord rest n
    case [] then None {}
    end
end

recursive let getName: [DocTree] -> { word: String, rest: [DocTree]} = use TokenReader in lam sons.
    switch sons
    case [DocTreeLeaf { token = TokenWord { content = "#var" } }, DocTreeLeaf { token = TokenStr { between = name } } ] ++ rest then
        { word = name, rest = rest }
    case [DocTreeLeaf { token = TokenWord { content = name } }] ++ rest then
        { word = name, rest = rest }
    case [_] ++ sons then getName sons
    end
end

-- Extracts the type signature from a reversed list of string tokens.
let strExtractType = use TokenReader in lam typedef.
    recursive let strExtractType = lam typedef.
     switch typedef
        case [] | ["in"] then ""
        case [x, "in"] | [x] then x
        case [current] ++ rest then
            let res = strExtractType rest in
            switch (current, res)
            case (_, "," ++ _) | ("{", "}" ++ _) | ("[", _) | (_, "]" ++ _) | ("(", _) | (_, ")" ++ _) | (_, ":" ++ _) then
                concat current res
            case (current, _) then join [current, " ", res]
            end
        end in strExtractType (reverse typedef)

-- Extracts the type signature from a list of syntax tree nodes.
let extractType = use TokenReader in lam typedef.
    strExtractType (foldl
        (lam a. lam w.
            match w with DocTreeLeaf { token = TokenWord { content = content } } then cons content a
            else a
         ) [] typedef)

-- Extracts parent names from a list of syntax tree nodes.
-- Stops when encountering 'end', 'type', or a few other keywords.
recursive let extractParents = lam words.
    match nthWord words 0 with Some { word = w, rest = words } then
        switch w
        case "end" | "type" | "sem" | "syn" | "con" then []
        case "=" | "+" then extractParents words
        case name then cons name (extractParents words)
        end
    else [] 
end

-- Skips any 'use' declarations in the syntax tree and returns the remaining nodes.
recursive let skipUseIn : [DocTree] -> [DocTree] = lam sons.
    match nthWord sons 0 with
    Some { word = "use", rest = sons } then
        match (nthWord sons 1) with Some { rest = sons } then
            skipUseIn sons
        else
            warn "The last word of the stream is a use without any name after.";
            []
    else sons
end

-- Extracts variant names from a stream of syntax tree nodes starting with '|'.
-- Returns a list of the variants as strings.
let extractVariants : [DocTree] -> [String] = lam stream.
    recursive let extractVariants : [DocTree] -> Option [String] -> [String] = lam stream. lam typeAcc.
        switch (nthWord stream 0, typeAcc)
        case (Some { word = "|", rest = stream }, Some typeAcc) then cons (strExtractType typeAcc) (extractVariants stream (Some []))
        case (Some { word = "|", rest = stream }, None {}) then extractVariants stream (Some [])
        case (Some { word = "->", rest = stream }, Some typeAcc) then cons (strExtractType typeAcc) (extractVariants stream (None {}))
        case (Some { word = word, rest = stream }, Some typeAcc) then extractVariants stream (Some (cons word typeAcc))
        case (Some { rest = stream }, None {}) then extractVariants stream (None {})
        case (None {}, Some typeAcc) then [strExtractType typeAcc]
        case (None {}, None {}) then []
        end
        
    in extractVariants stream (None {})

-- Extracts argument names from a lambda expression represented as syntax tree nodes.
-- Returns a list of parameter names.
recursive let extractParams = lam sons.
    switch nthWord sons 0 
    case Some { word = "lam", rest = rest } then
        let res = switch getName rest
        case { word = ".", rest = rest} then { word = "_", rest = rest }
        case { word = word, rest = rest} then
            recursive let goToPoint = lam sons.
                switch nthWord sons 0
                case Some { rest = rest, word = "." } then rest
                case Some { rest = rest } then goToPoint rest
                case None {} then
                    warn "While extracting the let arguments, we detected a pointless lamda function declaration.";
                    []
                end in
            { word = word, rest = goToPoint rest }
        end in
        cons res.word (extractParams res.rest)
    case _ then []
    end
end
