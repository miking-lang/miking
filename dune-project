(lang dune 2.0)
(generate_opam_files true)
(name boot)
(maintainers "David Broman <dbro@kth.se>")

(package
 (name boot)
 (synopsis "The Miking boot interpreter")
 (description "\| Miking is a meta language-system for creating DSLs.
              "\| This is the Miking bootstrap interpreter.
 )
 (depends
  dune
  batteries
  linenoise))
