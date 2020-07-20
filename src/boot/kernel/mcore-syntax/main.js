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

                setType("atom")(
                    "false",
                    "true"
                );

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



            return {
                startState: function ()  { return { f: normal }; },
                copyState:  function (s) { return { f: s.f }; },

                token: function(stream, state) {
                    var t = state.f(stream, function(s) { state.f = s; });
                    var w = stream.current();
                    return wellKnownWords.hasOwnProperty(w) ? wellKnownWords[w] : t;
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
