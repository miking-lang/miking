(define-module (miking)
 #:use-module (guix build-system ocaml)
 #:use-module (guix gexp)
 #:use-module (guix git-download)
 #:use-module (guix packages)
 ;; #:use-module (gnu packages compression)
 ;; #:use-module (gnu packages maths)
 #:use-module (gnu packages ocaml))

(define-public miking
  (package
    (name "miking")
    (version "0.0.1")
    (source
     ;; (local-file "/home/aathn/Documents/projects/miking/miking" #:recursive? #t)
     (origin
       (method git-fetch)
       (uri (git-reference
             (url "https://github.com/miking-lang/miking")
             (commit "fb0e67d781cb24b8c2d25693286054a845d64112")))
       (file-name (git-file-name name version))
       (sha256
        (base32
         "16ixfrrn9ns3ypr7c4krpham1lx32i801d12yv0f4y3fl8fn5vv2"))))
    (build-system ocaml-build-system)
    (arguments
     '(#:tests? #f
       #:phases
       (modify-phases %standard-phases
         (delete 'configure)
         (add-before 'build 'fixup-makescript
           (lambda _
               (substitute* "make.sh"
                 (("OCAMLPATH=") "OCAMLPATH=$OCAMLPATH:"))))
         (replace 'install
           (lambda* (#:key inputs outputs #:allow-other-keys)
             (let* ((out (assoc-ref outputs "out"))
                    (bin (string-append out "/bin"))
                    (lib (string-append out "/lib")))
               (invoke "dune" "install" "--prefix" out "--libdir"
                       (string-append lib "/ocaml/site-lib"))
               (install-file "build/mi" bin)
               (mkdir-p (string-append lib "/mcore"))
               (install-file "stdlib" (string-append lib "/mcore"))
               (wrap-program (string-append bin "/mi")
                 `("OCAMLPATH" ":" prefix (,(string-append lib "/ocaml/site-lib")))
                 `("PATH" ":" prefix (,bin)))))))))
    (propagated-inputs (list ocaml dune ocaml-linenoise))
    (inputs
     (list
   ;; openblas
   ;; zlib
   ; python               ;; python
   ; sundials suitesparse ;; sundials
   ; zeromq               ;; jupyter
   ; fswatch              ;; ipm server
      ))
    (synopsis "")
    (description "")
    (home-page "")
    (license #f)))
