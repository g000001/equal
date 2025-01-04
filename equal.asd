(in-package :asdf)

(defsystem equal
  :version "20200109"
  :description ":TEST #'EQUAL"
  :long-description ":TEST #'EQUAL"
  :author "CHIBA Masaomi"
  :maintainer "CHIBA Masaomi"
  :license "Unlicense"
  :serial t
  :components ((:file "equal")))

(defmethod perform :after ((o load-op) (c (eql (find-system 'equal))))
  (let ((name "https://github.com/g000001/equal")
        (nickname 'equal))
    (if (and (find-package nickname)
             (not (eq (find-package nickname)
                      (find-package name))))
        (warn "~A: A package with name ~A already exists." name nickname)
        (rename-package name name `(,nickname)))))
