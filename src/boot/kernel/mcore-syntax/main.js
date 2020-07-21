// CodeMirror, copyright (c) by Marijn Haverbeke and others
// Distributed under an MIT license: https://codemirror.net/LICENSE
// This mode is derived from the Haskell CodeMirror mode.

define(function() {
    "use strict";

    function load_ipython_extension() {
        CodeMirror.defineMode("mcore", function(_config, modeConfig) {

            function switchState(source, setState, f) {
                setState(f);
                return f(source, setState);
            }

            var smallRE = /[a-z_]/;
            var largeRE = /[A-Z]/;
            var digitRE = /\d/;
            var idRE = /[a-z_A-Z0-9]/;
            var whiteCharRE = /[ \t\v\f]/; // newlines are handled in tokenizer

            function normal(source, setState) {
                if (source.eatWhile(whiteCharRE)) {
                    return null;
                }

                var ch = source.next();
                if (ch == '\'') {
                    source.eat('\\');
                    source.next();
                    if (source.eat('\'')) {
                        return "string";
                    }
                    return "string error";
                }

                if (ch == '"') {
                    return switchState(source, setState, stringLiteral);
                }

                if (largeRE.test(ch)) {
                    source.eatWhile(idRE);
                    return "variable-2";
                }

                if (smallRE.test(ch)) {
                    source.eatWhile(idRE);
                    return "variable";
                }

                if (digitRE.test(ch)) {
                    source.eatWhile(digitRE);
                    return "number";
                }

                if (ch == '-' && source.eat(/-/)) {
                    source.skipToEnd();
                    return "comment";
                }

                return null;
            }

            function stringLiteral(source, setState) {
                while (!source.eol()) {
                    var ch = source.next();
                    if (ch == '"') {
                        setState(normal);
                        return "string";
                    }
                }
                setState(normal);
                return "string error";
            }

            function definition(source, setState) {
                if (source.eatWhile(whiteCharRE)) {
                  return null;
                }

                var ch = source.next();
                var t = null;
                if (largeRE.test(ch) || smallRE.test(ch)) {
                    source.eatWhile(idRE);
                    t = "def";
                }
                setState(normal);
                return t;
            }

            var wellKnownWords = (function() {
                var wkw = {};
                function setType(t) {
                    return function () {
                        for (var i = 0; i < arguments.length; i++)
                            wkw[arguments[i]] = t;
                    };
                }

                setType("keyword")(
                    "con",
                    "else",
                    "end",
                    "fix",
                    "if",
                    "in",
                    "lam",
                    "lang",
                    "let",
                    "match",
                    "recursive",
                    "sem",
                    "syn",
                    "then",
                    "type",
                    "use",
                    "utest",
                    "with"
                );

                setType("builtin")(
                    "false",
                    "true"
                );

                setType("builtin")(
                    "not","and","or",
                    "addi","subi","muli",
                    "divi","modi","negi",
                    "lti","leqi","gti","geqi",
                    "eqi","neqi",
                    "slli","srli","srai",
                    "arity",
                    "addf","subf","mulf",
                    "divf","negf",
                    "ltf","leqf","gtf","geqf",
                    "eqf","neqf",
                    "floorfi","ceilfi","roundfi",
                    "int2float","string2float",
                    "char2int","int2char",
                    "makeSeq","length","concat",
                    "get","set",
                    "cons","snoc",
                    "splitAt","reverse",
                    "print","dprint",
                    "argv",
                    "readFile","writeFile",
                    "fileExists","deleteFile",
                    "error",
                    "eqs","gensym",
                    "pycall","pyimport","pyconvert"
                )

                setType("meta")(
                    "mexpr",
                    "include",
                    "never"
                );

                var override = modeConfig.overrideKeywords;
                if (override) for (var word in override) if (override.hasOwnProperty(word))
                    wkw[word] = override[word];

                return wkw;
            })();

            var definitionWords = [
              "con",
              "lang",
              "let",
              "sem",
              "syn",
              "type"
            ]

            var strongIndentationWords = [
              "lang"
            ]

            var indentationWords = strongIndentationWords.concat([
              "then",
              "else"
              ]
            )

            var indentLength = _config.indentUnit;

            function resetIndentation(stream, state){
                if (!state.strongIndent){
                    state.indent = stream.indentation();
                }
                if (stream.eol()) {
                    state.strongIndent = false;
                }
            }

            function setIndentation(state, word){
                if (indentationWords.includes(word)){
                    state.indent += indentLength;
                    if (strongIndentationWords.includes(word)){
                        state.strongIndent = true;
                    }
                }
            }

            return {
                startState: function ()  { return { f: normal, indent: 0, strongIndent: false }; },
                copyState:  function (s) { return { f: s.f, indent: s.indent, strongIndent: s.strongIndent }; },

                token: function(stream, state) {
                    var t = state.f(stream, function(s) { state.f = s; });
                    var w = stream.current();
                    resetIndentation(stream, state);
                    if (wellKnownWords.hasOwnProperty(w)){
                      if (definitionWords.includes(w)){
                        state.f = definition;
                      }
                      setIndentation(state, w);
                      return wellKnownWords[w];
                    } else {
                      return t;
                    }
                },

                indent: function(state, textAfter) {
                    return state.indent;
                },

                lineComment: "--"
            };

        });

        CodeMirror.defineMIME(
            "text/x-mcore",
            {name: "MCore", mime: "text/x-mcore", mode: "mcore", ext: [".mc"]}
        );
    }

    return {
        load_ipython_extension: load_ipython_extension
    };
});
