;;; mcore-mode.el

;;;;;;;;;;;;;;;;;;
;; Highlighting ;;
;;;;;;;;;;;;;;;;;;

;; Please keep this list sorted
(setq mcore-keywords
     '(
       "Lam"
       "else"
       "end"
       "fix"
       "if"
       "in"
       "lam"
       "lang"
       "let"
       "match"
       "sem"
       "syn"
       "then"
       "utest"
       "with"
      ))

(setq mcore-constants
      '(
        "false"
        "true"
        ))

(setq mcore-primitives
      '( )) ;; Primitive types (intensionally left blank)

(setq mcore-operators
     '( )) ;; Intensionally left blank

(setq mcore-keywords-regexp (regexp-opt mcore-keywords 'symbols))
(setq mcore-operators-regexp (regexp-opt mcore-operators 'symbols))
(setq mcore-constants-regexp (regexp-opt mcore-constants 'symbols))
(setq mcore-primitives-regexp (regexp-opt mcore-primitives 'symbols))

(setq mcore-types-regexp "\\<[[:upper:]][[:word:]]*\\>")

(setq mcore-font-lock-keywords
     `(
       (,mcore-keywords-regexp   . font-lock-keyword-face)
       (,mcore-constants-regexp  . font-lock-constant-face)
       (,mcore-primitives-regexp . font-lock-type-face)
       (,mcore-operators-regexp  . font-lock-builtin-face)
       (,mcore-types-regexp      . font-lock-type-face)
       )
     )

(defvar mcore-mode-syntax-table nil "Syntax table for `mcore-mode'.")

(setq mcore-mode-syntax-table
     (let ( (synTable (make-syntax-table)))
       ;; Inline comment “// ...”
       ;; Inline comment “-- ...”
       (modify-syntax-entry ?/ ". 12a" synTable)
       (modify-syntax-entry ?- "_ 123" synTable)
       (modify-syntax-entry ?\n ">" synTable)
       synTable))

;;;;;;;;;;;;;;;;;
;; compilation ;;
;;;;;;;;;;;;;;;;;

(add-hook 'mcore-mode-hook
          (lambda ()
            (set (make-local-variable 'compile-command)
                 (concat "miking " (buffer-name)))))

(setq mcore-error-regexp
      '(mcore "\"\\(.*\\)\" \\([0-9]*\\):\\([0-9]*\\)" 1 2 3))
(add-hook 'compilation-mode-hook
          (lambda ()
            (add-to-list 'compilation-error-regexp-alist-alist mcore-error-regexp)
            (add-to-list 'compilation-error-regexp-alist 'mcore)))

;;;;;;;;;;;;;;;;;;;;;
;; mode definition ;;
;;;;;;;;;;;;;;;;;;;;;

(define-derived-mode mcore-mode prog-mode
 (setq font-lock-defaults '(mcore-font-lock-keywords))
 (setq mode-name "mcore")
 )

;; Open “*.mcore” in mcore-mode
(add-to-list 'auto-mode-alist '("\\.mc\\'" . mcore-mode))

(provide 'mcore-mode)
;;; mcore-mode.el ends here
