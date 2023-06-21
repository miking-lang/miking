(define-module (miking)
  #:use-module (guix build-system dune)
  #:use-module (guix build-system gnu)
  #:use-module (guix build-system ocaml)
  #:use-module (guix build-system trivial)
  #:use-module (guix gexp)
  #:use-module (guix git-download)
  #:use-module (guix packages)
  #:use-module (guix utils)
  #:use-module ((guix licenses) #:prefix license:)
  #:use-module (gnu packages base)
  #:use-module (gnu packages commencement)
  #:use-module (gnu packages compression)
  ;; #:use-module (gnu packages java)
  #:use-module (gnu packages maths)
  ;; #:use-module (gnu packages node)
  #:use-module (gnu packages python)
  #:use-module (gnu packages python-xyz)
  #:use-module (gnu packages ocaml))

(define-public ocaml-ISO8601
  (package
    (name "ocaml-ISO8601")
    (version "0.2.6")
    (source (origin
              (method git-fetch)
              (uri (git-reference
                    (url "https://github.com/ocaml-community/ISO8601.ml")
                    (commit version)))
              (sha256
               (base32
                "0nzadswspizi7s6sf67icn2xgc3w150x8vdg5nk1mjrm2s98n6d3"))))
    (build-system dune-build-system)
    (arguments
     '(#:tests? #f)) ;; Tests import Pervasives module, unavailable in OCaml 5 (?)
    (propagated-inputs (list ocaml-odoc))
    (native-inputs (list ocaml-ounit))
    (home-page "https://github.com/ocaml-community/ISO8601.ml/")
    (synopsis "ISO 8601 and RFC 3339 date parsing for OCaml")
    (description
     "OCaml parser and printer for date-times in ISO8601 and RFC 3339")
    (license license:expat)))

(define-public ocaml-ocb
  (package
    (name "ocaml-ocb")
    (version "0.2")
    (source (origin
              (method git-fetch)
              (uri (git-reference
                    (url "https://github.com/OCamlPro/ocb")
                    (commit version)))
              (sha256
               (base32
                "1nk90jax91ld8qd36qi408mll8a7w1d60fa2qdsnff7cldwixc1d"))))
    (build-system dune-build-system)
    (propagated-inputs (list ocaml-odoc))
    (home-page "https://ocamlpro.github.io/ocb/")
    (synopsis "SVG badge generator")
    (description
     "An OCaml library for SVG badge generation.  There's also a command-line tool
provided.")
    (license license:isc)))

(define-public ocaml-npy
  (package
    (name "ocaml-npy")
    (version "0.0.9")
    (source (origin
              (method git-fetch)
              (uri (git-reference
                    (url "https://github.com/LaurentMazare/npy-ocaml")
                    (commit version)))
              (sha256
               (base32
                "1fryglkm20h6kdqjl55b7065b34bdg3g3p6j0jv33zvd1m5888m1"))))
    (build-system dune-build-system)
    (native-inputs (list zlib python-wrapper python-numpy))
    (propagated-inputs (list camlzip))
    (home-page "https://github.com/LaurentMazare/npy-ocaml")
    (synopsis "Numpy npy file format reading/writing for OCaml")
    (description
     "A library providing simple read/write function using the numpy npy/npz
file formats.  These can be used to save a bigarray to disk and then load it
from python using numpy.")
    (license license:asl2.0)))

(define-public ocaml-toml
  (package
    (name "ocaml-toml")
    (version "7.1.0")
    (source (origin
              (method git-fetch)
              (uri (git-reference
                    (url "https://github.com/ocaml-toml/to.ml")
                    (commit version)))
              (sha256
               (base32
                "0z2873mj3i6h9cg8zlkipcjab8jympa4c4avhk4l04755qzphkds"))))
    (build-system dune-build-system)
    (propagated-inputs (list ocaml-odoc ocaml-ISO8601))
    (native-inputs
     (list ocaml-menhir ocaml-ounit2 ocaml-mdx ocaml-bisect-ppx ocaml-ocb))
    (home-page "https://ocaml-toml.github.io/To.ml/")
    (synopsis "Library for TOML with a parser, a serializer and a printer")
    (description
     "toml is an OCaml library providing a parser, a serializer and a printer for
TOML, a minimal configuration file format.  Helpful getters to retrieve data as
OCaml primitive types are also supplied.")
    (license license:lgpl3)))

(define-public ocaml-owl
  (package
    (name "ocaml-owl")
    (version "1.1")
    (source (origin
              (method git-fetch)
              (uri (git-reference
                    (url "https://github.com/owlbarn/owl")
                    (commit version)))
              (sha256
               (base32
                "08jvgf1fd7d28cxxjifx4ikmwcbfbiyw0sivw3xy4vdzvbyc9xw9"))))
    (build-system dune-build-system)
    (propagated-inputs (list openblas zlib ocaml-ctypes ocaml-npy ocaml-compiler-libs))
    (native-inputs (list ocaml-alcotest ocaml-base ocaml-stdio))
    (home-page "https://github.com/owlbarn/owl")
    (synopsis "OCaml Scientific and Engineering Computing")
    (description
     "Owl is an OCaml numerical library.  It supports N-dimensional
arrays, both dense and sparse matrix operations, linear algebra,
regressions, fast Fourier transforms, and many advanced mathematical
and statistical functions (such as Markov chain Monte Carlo methods).
Recently, Owl has implemented algorithmic differentiation which
simplifies developing machine learning and neural network
algorithms.")
    (license license:expat)))

(define-public ocaml-base-bytes
  (package
    (name "ocaml-base-bytes")
    (version "base")
    (source #f)
    (build-system trivial-build-system)
    (arguments
     (list
      #:modules '((guix build utils))
      #:builder
      #~(begin
          (use-modules (guix build utils))
          (let ((bytes (string-append #$output "/lib/ocaml/bytes")))
            (mkdir-p bytes)
            (call-with-output-file (string-append bytes "/META")
              (lambda (port)
                (format port "name=\"bytes\"
version=\"[distributed with OCaml 4.02 or above]\"
description=\"dummy backward-compatibility package for mutable strings\"
requires=\"\"
")))))))
    (home-page "https://opam-4.ocaml.org/packages/base-bytes/")
    (synopsis "Dummy backward-compatibility package for mutable strings")
    (description
     "A dummy package for depending on the base Bytes module distributed with
the OCaml compiler.")
    (license license:expat)))


(define-public miking
  (package
    (name "miking")
    (version "0.0.1")
    (source
     (origin
       (method git-fetch)
       (uri (git-reference
             (url "https://github.com/miking-lang/miking")
             (commit "fb0e67d781cb24b8c2d25693286054a845d64112")))
       (file-name (git-file-name name version))
       (sha256
        (base32
         "16ixfrrn9ns3ypr7c4krpham1lx32i801d12yv0f4y3fl8fn5vv2"))))
    (build-system gnu-build-system)
    (propagated-inputs
     (list
      ocaml-5.0
      ocaml5.0-dune
      (package-with-ocaml5.0 ocaml-linenoise)
      gcc-toolchain

      coreutils                           ;; For sys.mc (mkdir, echo, rm, ...)
      ocaml-base-bytes                    ;; Needed for ocaml5.0-{lwt,owl}
      (package-with-ocaml5.0 ocaml-lwt)   ;; For async-ext.mc
      (package-with-ocaml5.0 ocaml-owl)   ;; For dist-ext.mc
      (package-with-ocaml5.0 ocaml-toml)  ;; For toml-ext.mc
      which                               ;; For sys.mc

      ;; (package-with-ocaml5.0 ocaml-pyml)  ;; For boot python bindings
      ;; node-lts                            ;; For javascript backend
      ;; (list openjdk "jdk"))               ;; For java backend
     ))
    (arguments
     `(#:test-target "test-compile"
       #:phases
       (modify-phases %standard-phases
         (delete 'configure)
         (add-before 'build 'fixup-makescript
           (lambda _
             (substitute* "make.sh"
               (("OCAMLPATH=") "OCAMLPATH=$OCAMLPATH:"))
             (substitute* "test-boot.mk"
               (("MCORE_LIBS=") "OCAMLPATH=${OCAMLPATH}:`pwd`/build/lib MCORE_LIBS="))))
         (replace 'install
           (lambda* (#:key outputs #:allow-other-keys)
             (let* ((out (assoc-ref outputs "out"))
                    (bin (string-append out "/bin"))
                    (lib (string-append out "/lib")))
               (invoke "dune" "install" "--prefix" out "--libdir"
                       (string-append lib "/ocaml/site-lib"))
               (install-file "build/mi" bin)
               (copy-recursively "stdlib" (string-append lib "/mcore/stdlib"))))))))
    (synopsis "Meta language system for creating embedded DSLs.")
    (description "Miking (Meta vIKING) is a meta language system for creating
embedded domain-specific and general-purpose languages.  The system features
a polymorphic core calculus and a DSL definition language where languages
can be extended and composed from smaller fragments.")
    (home-page "https://miking.org")
    (license license:expat)))
