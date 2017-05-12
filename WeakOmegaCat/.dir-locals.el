((coq-mode
  . ((eval . 
	   (progn
	     (make-local-variable 'coq-prog-args)
         (setq coq-prog-name "~/Prog/coq/IR/coq/bin/coqtop")
	      (if (not (memq 'agda-input features))
                 (load (concat "~/coq/UniMath/" "emacs/agda/agda-input")))
             (if (not (member '("chimney" "╝") agda-input-user-translations))
                 (progn
                   (setq agda-input-user-translations (cons '("chimney" "╝") agda-input-user-translations))
                   (agda-input-setup)))
             (set-input-method "Agda")
	     (setq coq-prog-args `("-emacs" "-indices-matter" "-R" ,(expand-file-name (locate-dominating-file buffer-file-name ".dir-locals.el")) "WeakOmegaCat" )))))))
