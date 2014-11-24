(require 'org)
;; (require 'ox-latex)
;; (defsubst org-fix-ellipsis-at-bol () nil)
(setq org-latex-listings 'minted)
(setq org-latex-minted-options
      '(("frame" "lines") ("linenos=true")))
;; (setq org-confirm-babel-evaluate nil)
