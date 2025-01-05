(cl:in-package cl-user)

(defpackage "https://github.com/g000001/equal"
  (:use)
  (:export
   adjoin
   assoc
   count
   delete
   delete-duplicates
   find
   intersection
   make-hash-table
   member
   mismatch
   nintersection
   nset-difference
   nset-exclusive-or
   nsublis
   nsubst
   nsubstitute
   nunion
   position
   pushnew
   rassoc
   remove
   remove-duplicates
   search
   set-difference
   set-exclusive-or
   sublis
   subsetp
   subst
   substitute
   tree-equal
   union))

(defpackage "https://github.com/g000001/equal#internals"
  (:use "https://github.com/g000001/equal" cl)
  (:shadowing-import-from
   "https://github.com/g000001/equal"
   adjoin
   assoc
   count
   delete
   delete-duplicates
   find
   intersection
   make-hash-table
   member
   mismatch
   nintersection
   nset-difference
   nset-exclusive-or
   nsublis
   nsubst
   nsubstitute
   nunion
   position
   pushnew
   rassoc
   remove
   remove-duplicates
   search
   set-difference
   set-exclusive-or
   sublis
   subsetp
   subst
   substitute
   tree-equal
   union))

(in-package "https://github.com/g000001/equal#internals")

;; Copyright (C) 2002-2004, Yuji Minejima <ggb01164@nifty.ne.jp>
;; ALL RIGHTS RESERVED.
;;
;; $Id: share.lisp,v 1.10 2004/09/02 06:59:43 yuji Exp $
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;; 
;;  * Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;;  * Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in
;;    the documentation and/or other materials provided with the
;;    distribution.
;; 
;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(deftype proper-list () '(satisfies proper-list-p))
(deftype proper-sequence () '(satisfies proper-sequence-p))
(deftype string-designator () '(or character symbol string))
(deftype package-designator () '(or string-designator package))
(deftype function-designator () '(or symbol function))
(deftype extended-function-designator ()
  '(or function (satisfies function-name-p)))
(deftype character-designator-simbol ()
  '(satisfies character-designator-symbol-p))

(defun character-designator-symbol-p (object)
  (and (symbolp object) (= (length (symbol-name object)) 1)))

(defun function-name-p (object)
  (or (symbolp object)
      (and (consp object)
	   (eq (car object) 'setf)
	   (symbolp (cadr object))
	   (null (cddr object)))))

(defun proper-list-p (object)
  (when (listp object)
    (do ((fast object (cddr fast))
	 (slow object (cdr slow)))
	(nil)
      (when (atom fast)
	(return (null fast)))
      (when (atom (cdr fast))
	(return (null (cdr fast))))
      (when (and (eq fast slow) (not (eq fast object)))
	(return nil)))))

(defun proper-sequence-p (object)
  (or (vectorp object) (proper-list-p object)))

(defun error-circular-list (list)
  (error 'type-error :datum list :expected-type 'proper-list))

(defun error-index-too-large (sequence index)
  (error 'type-error
	 :datum index
	 :expected-type `(integer 0 ,(1- (length sequence)))))

(defmacro apply-key (key element)
  `(if ,key
       (funcall ,key ,element)
     ,element))


(defmacro do-sublist ((var list start end from-end result) &body body)
  (let ((rev (gensym))
	(i   (gensym))
	(x   (gensym)))
    `(symbol-macrolet ((,var (car ,x)))
       (if ,from-end
	   (let ((,rev nil))
	     (do ((x (nthcdr ,start ,list) (cdr x))
		  (i ,start (1+ i)))
		 ((>= i ,end))
	       (setq ,rev (cons x ,rev)))
	     (do* ((,rev ,rev (cdr ,rev))
		   (,x (car ,rev) (car ,rev)))
		 ((null ,rev) ,result)
	       ,@body))
	 (do ((,x (nthcdr ,start ,list) (cdr ,x))
	      (,i ,start (1+ ,i)))
	     ((>= ,i ,end) ,result)
	   ,@body)))))

(defmacro do-subvector ((var vector start end from-end result) &body body)
  (let ((i     (gensym))
	(step  (gensym))
	(limit (gensym)))
    `(symbol-macrolet ((,var (aref ,vector ,i)))
       (let ((,step (if ,from-end -1 1))
	     (,limit (if ,from-end (1- ,start) ,end)))
	 (do ((,i (if ,from-end (1- ,end) ,start) (+ ,i ,step)))
	     ((= ,i ,limit) ,result)
	  ,@body)))))

(defmacro do-subsequence ((var sequence-form start-form &optional end-form
			       from-end-form result-form) &body body)
  (let ((sequence (gensym))
	(start    (gensym))
	(end      (gensym)))
    `(let* ((,sequence ,sequence-form)
	    (,start ,start-form)
	    (,end (or ,end-form (length ,sequence))))
       (check-subsequence ,sequence ,start ,end)
       (etypecase ,sequence
	 (list
	  (do-sublist (,var ,sequence ,start ,end ,from-end-form ,result-form)
             ,@body))
	 (vector
	  (do-subvector (,var ,sequence ,start ,end ,from-end-form ,result-form)
	     ,@body))))))

(defun declarationp (expr)
  (and (consp expr) (eq (car expr) 'declare)))

(defun declarations-and-forms (body)
  (block nil
    (let ((decls nil)
	  (forms body))
      (tagbody
       top
	 (when (not (declarationp (car forms)))
	   (return (values (reverse decls) forms)))
	 (push (car forms) decls) (psetq forms (cdr forms))
	 (go top)))))


(defun required-argument ()
  (error "required argument not specified."))


(defun %symbol (designator)
  (if (symbolp designator)
      designator
      (error 'type-error :datum designator :expected-type 'symbol)))
(defun %keyword (designator)
  (intern (string designator) "KEYWORD"))
(defun %list (designator)
  (if (listp designator)
      designator
      (list designator)))
(defun symbol-list (designator) (mapcar #'%symbol (%list designator)))
(defun string-list (designator) (mapcar #'string (%list designator)))



(defun store-value-report (stream place)
  (format stream "Supply a new value for ~S." place))
(defun store-value-interactive ()
  (format *query-io* "~&Type a form to be evaluated:~%")
  (list (eval (read *query-io*))))



(defun mapappend (function &rest lists)
  (apply #'append (apply #'mapcar function lists)))

(define-condition simple-program-error (simple-condition program-error) ())

(define-modify-macro appendf (&rest args)
   append "Append onto list")


;; Copyright (C) 2002-2004, Yuji Minejima <ggb01164@nifty.ne.jp>
;; ALL RIGHTS RESERVED.
;;
;; $Id: sequence.lisp,v 1.42 2004/02/20 07:23:42 yuji Exp $
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;; 
;;  * Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;;  * Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in
;;    the documentation and/or other materials provided with the
;;    distribution.
;; 
;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(defun check-sequence-access (sequence index)
  (check-type sequence proper-sequence)
  (check-type index (integer 0))
  (unless (< index (length sequence))
    (error-index-too-large sequence index)))

(defun check-subsequence (sequence start end)
  (check-type sequence proper-sequence)
  (check-type start (integer 0))
  (check-type end (integer 0)))

(defun count (item sequence
		   &key from-end (start 0) end key (test #'equal) test-not)
  "Count the number of ITEM in SEQUENCE bounded by START and END."
  (when test-not (setq test (complement test-not)))
  (count-if #'(lambda (arg) (funcall test item arg))
	    sequence :from-end from-end :start start :end end :key key))

(defun find (item sequence
		  &key from-end (test #'equal) test-not (start 0) end key)
  "Return the first element in SEQUENCE satisfying TEST or TEST-NOT."
  (when test-not (setq test (complement test-not)))
  (find-if #'(lambda (arg) (funcall test item arg))
	   sequence :from-end from-end :start start :end end :key key))

(defun position (item sequence
		  &key from-end (test #'equal) test-not (start 0) end key)
  "Return the position of an element in SEQUENCE equal to ITEM by TEST."
  (when test-not (setq test (complement test-not)))
  (position-if #'(lambda (arg) (funcall test item arg))
	       sequence :from-end from-end :start start :end end :key key))

(defun make-iterator (sequence start end length from-end)
  (check-subsequence sequence start end)
  (if (listp sequence)
      (let* ((head (if from-end
		       (nthcdr (- length end) (reverse sequence))
		     (nthcdr start sequence)))
	     (x head))
	(values #'(lambda () (prog1 (car x) (setq x (cdr x))))
		#'(lambda () (setq x head))))
    (let* ((from (if from-end (1- end) start))
	   (i from)
	   (step (if from-end -1 1)))
      (values #'(lambda () (prog1 (aref sequence i) (setq i (+ i step))))
	      #'(lambda () (setq i from))))))

(defun search (sequence1 sequence2 &key from-end (test #'equal) test-not key
			  (start1 0) (start2 0) end1 end2)
  "Return the first position in SEQUENCE2 that matches SEQUENCE1."
  (when test-not (setq test (complement test-not)))
  (let* ((length1 (length sequence1))
	 (end1 (or end1 length1))
	 (end2 (or end2 (length sequence2)))
	 (width1 (- end1 start1))
	 (last-match nil))
    (multiple-value-bind (get1 reset1)
	(make-iterator sequence1 start1 end1 length1 nil)
      (etypecase sequence2
	(null (when (zerop length1) 0))
	(cons (do ((x (nthcdr start2 sequence2) (cdr x))
		   (i start2 (1+ i)))
		  ((> i (- end2 width1)) (when from-end last-match))
		(funcall reset1)
		(do ((xx x (cdr xx))
		     (j 0 (1+ j)))
		    ((>= j width1) (if from-end
				       (setq last-match i)
				     (return-from search i)))
		  (unless (funcall test (apply-key key (funcall get1))
				        (apply-key key (car xx)))
		    (return)))))
	(vector (do ((i start2 (1+ i)))
		    ((> i (- end2 width1)) (when from-end last-match))
		  (funcall reset1)
		  (do ((ii i (1+ ii))
		       (j 0 (1+ j)))
		      ((>= j width1) (if from-end
					 (setq last-match i)
				       (return-from search i)))
		    (unless (funcall test (apply-key key (funcall get1))
				          (apply-key key (aref sequence2 ii)))
		      (return)))))))))

(defun mismatch (sequence1 sequence2 &key from-end (test #'equal) test-not key
			   (start1 0) (start2 0) end1 end2)
  "Return the first position where SEQUENCE1 and SEQUENCE2 differ."
  (when test-not (setq test (complement test-not)))
  (let* ((length1 (length sequence1))
	 (length2 (length sequence2))
	 (end1 (or end1 length1))
	 (end2 (or end2 length2))
	 (width1 (- end1 start1))
	 (width2 (- end2 start2))
	 (width (min width1 width2))
	 (s1 (if from-end (- end1 width) start1))
	 (e1 (if from-end end1 (+ start1 width))))
    (multiple-value-bind (get2 reset2)
	(make-iterator sequence2 start2 end2 length2 from-end)
      (declare (ignore reset2))
      (let ((i1 (if from-end (1- end1) start1))
	    (step (if from-end -1 1)))
	(do-subsequence (element1 sequence1 s1 e1 from-end
                         (cond ((= width1 width2) nil)
			       ((< width1 width2) (if from-end 0 end1))
			       (t (if from-end
				      (- end1 width2)
				    (+ start1 width2)))))
            (unless (funcall test (apply-key key element1)
			     (apply-key key (funcall get2)))
	      (return (if from-end (1+ i1) i1)))
	    (incf i1 step))))))

(defun nsubstitute (newitem olditem sequence &key from-end (test #'equal) test-not
			    (start 0) end count key)
  "Modify SEQUENCE substituting NEWITEM for elements euqal to OLDITEM."
  (when test-not (setq test (complement test-not)))
  (nsubstitute-if newitem #'(lambda (item) (funcall test olditem item))
		  sequence :from-end from-end :start start :end end
		  :count count :key key))

(defun substitute (newitem olditem sequence &key from-end (test #'equal) test-not
			   (start 0) end count key)
  "Return a copy of SEQUENCE with elements euqal to OLDITEM replaced with NEWITEM."
  (nsubstitute newitem olditem (copy-seq sequence) :from-end from-end :test test
	       :test-not test-not :start start :end end :count count :key key))

(defun delete (item sequence &key from-end (test #'equal) test-not (start 0) end
		    count key)
  "Modify SEQUENCE by deleting elements equal to ITEM."
  (when test-not (setq test (complement test-not)))
  (delete-if #'(lambda (arg) (funcall test item arg)) sequence
	     :from-end from-end :start start :end end :count count :key key))

(defun remove (item sequence &key from-end (test #'equal) test-not (start 0)
		    end count key)
  "Return a copy of SEQUENCE with elements equal to ITEM removed."
  (when test-not (setq test (complement test-not)))
  (remove-if #'(lambda (arg) (funcall test item arg)) sequence
	     :from-end from-end :start start :end end :count count :key key))

(defun list-delete-duplicates (test list start end key)
  (check-type list proper-list)
  (let* ((head (cons nil list))
	 (splice head)
	 (tail (when end (nthcdr end list))))
    (flet ((list-member (list)
	      (do ((x (cdr list) (cdr x))
		   (item (car list)))
		  ((eq x tail) nil)
		(when (funcall test (apply-key key item) (apply-key key (car x)))
		  (return t)))))
      (do ((i 0 (1+ i))
	   (x list (cdr x)))
	  ((endp x) (rplacd splice nil) (cdr head))
	(unless (and (<= start i) (or (null end) (< i end)) (list-member x))
	  (setq splice (cdr (rplacd splice x))))))))

(defun vector-delete-duplicates (test vector start end key)
  (let* ((length (length vector))
	 (end (or end length))
	 (i 0))
    (flet ((vector-member (item j)
             (do ((k (1+ j) (1+ k)))
                 ((>= k end) nil)
               (when (funcall test (apply-key key item)
                              (apply-key key (aref vector k)))
                 (return t)))))
      (do* ((j 0 (1+ j))
	    element)
           ((>= j length))
	(setq element (aref vector j))
	(unless (and (<= start j) (< j end) (vector-member element j))
	  (setf (aref vector i) element)
	  (incf i)))
      (cond
        ((array-has-fill-pointer-p vector)
         (setf (fill-pointer vector) i)
         vector)
        ((adjustable-array-p vector) (adjust-array vector i))
        (t (subseq vector 0 i))))))

(defun delete-duplicates (sequence &key from-end (test #'equal) test-not
				   (start 0) end key)
  "Modify SEQUENCE deleting redundant elements."
  (when test-not (setq test (complement test-not)))
  (if from-end
      (let ((length (length sequence)))
	(nreverse (delete-duplicates (nreverse sequence) :test test :key key
				     :start (- length (or end length))
				     :end (- length start))))
    (etypecase sequence
      (null nil)
      (cons (list-delete-duplicates     test sequence start end key))
      (vector (vector-delete-duplicates test sequence start end key)))))

(defun remove-duplicates (sequence &key from-end (test #'equal) test-not
				   (start 0) end key)
  "Return a copy of SEQUENCE with redundant elements removed."
  (delete-duplicates (copy-seq sequence) :from-end from-end :key key
		     :test test :test-not test-not :start start :end end))

(defmacro do-sequences ((var sequences &optional (result nil)) &body body)
  (let ((seq-list (gensym))
	(i        (gensym))
	(min      (gensym)))
    `(let* ((,seq-list (copy-seq ,sequences))
	    (,var (make-list (list-length ,seq-list) :initial-element nil))
	    (,min (if ,seq-list (reduce #'min ,seq-list :key #'length) 0)))
       (dotimes (,i ,min ,result)
	 (do* ((src ,seq-list (cdr src))
	       (seq (car src) (car src))
	       (dest ,var (cdr dest)))
	     ((null src))
	   (rplaca dest (if (consp seq)
			    (progn
			      (rplaca src (cdr seq))
			      (car seq))
			  (aref seq ,i))))
	 ,@body))))

;; Copyright (C) 2002-2004, Yuji Minejima <ggb01164@nifty.ne.jp>
;; ALL RIGHTS RESERVED.
;;
;; $Id: cons.lisp,v 1.4 2004/02/20 07:23:42 yuji Exp $
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;; 
;;  * Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;;  * Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in
;;    the documentation and/or other materials provided with the
;;    distribution.
;; 
;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(defun member (item list &key key (test #'equal) test-not)
  "Return the tail of LIST beginning with an element equal to ITEM."
  (when test-not
    (setq test (complement test-not)))
  (do ((here list (cdr here)))
      ((or (null here) (funcall test item (apply-key key (car here)))) here)))

(defun adjoin (item list &key key (test #'equal) test-not)
  "Add ITEM to LIST unless it is already a member."
  (when test-not
    (setq test (complement test-not)))
  (if (member (apply-key key item) list :key key :test test)
      list
    (cons item list)))

(defun assoc (item alist &key key (test #'equal) test-not)
  "Return the cons in ALIST whose car is equal (by TEST) to ITEM."
  (when test-not
    (setq test (complement test-not)))
  (dolist (pair alist nil)
    (when (and pair (funcall test item (apply-key key (car pair))))
      (return pair))))

(defun intersection (list-1 list-2 &key key (test #'equal) test-not)
  "Return the intersection of LIST-1 and LIST-2."
  (when test-not
    (setq test (complement test-not)))
  (let (result)
    (dolist (element list-1)
      (when (member (apply-key key element) list-2 :key key :test test)
	(push element result)))
    result))

(defun nintersection (list-1 list-2 &key key (test #'equal) test-not)
  "Return the intersection of LIST-1 and LIST-2 destructively modifying LIST-1."
  (when test-not
    (setq test (complement test-not)))
  (let* ((result (list nil))
	 (splice result))
    (do ((list list-1 (cdr list)))
	((endp list) (rplacd splice nil) (cdr result))
      (when (member (apply-key key (car list)) list-2 :key key :test test)
	(setq splice (cdr (rplacd splice list)))))))

(defun union (list-1 list-2 &key key (test #'equal) test-not)
  "Return the union of LIST-1 and LIST-2."
  (when test-not
    (setq test (complement test-not)))
  (let ((result list-2))
    (dolist (element list-1)
      (unless (member (apply-key key element) list-2 :key key :test test)
	(push element result)))
    result))

(defun nunion (list-1 list-2 &key key (test #'equal) test-not)
  "Return the union of LIST-1 and LIST-2 destructively modifying them."
  (when test-not
    (setq test (complement test-not)))
  (do* ((result list-2)
	(list-1 list-1)
	tmp)
      ((endp list-1) result)
    (if (member (apply-key key (car list-1)) list-2 :key key :test test)
	(setq list-1 (cdr list-1))
      (setq tmp (cdr list-1)
	    result (rplacd list-1 result)
	    list-1 tmp))))

(defun subsetp (list-1 list-2 &key key (test #'equal) test-not)
  "Return T if every element in LIST-1 is also in LIST-2."
  (when test-not
    (setq test (complement test-not)))
  (dolist (element list-1 t)
    (unless (member (apply-key key element) list-2 :key key :test test)
      (return nil))))

(defun set-difference (list-1 list-2 &key key (test #'equal) test-not)
  "Return the elements of LIST-1 which are not in LIST-2."
  (when test-not
    (setq test (complement test-not)))
  (let ((result nil))
    (dolist (element list-1)
      (unless (member (apply-key key element) list-2 :key key :test test)
	(push element result)))
    result))

(defun nset-difference (list-1 list-2 &key key (test #'equal) test-not)
  "Return the elements of LIST-1 which are not in LIST-2, modifying LIST-1."
  (when test-not
    (setq test (complement test-not)))
  (do* ((result nil)
	(list-1 list-1)
	tmp)
      ((endp list-1) result)
    (if (member (apply-key key (car list-1)) list-2 :key key :test test)
	(setq list-1 (cdr list-1))
      (setq tmp (cdr list-1)
	    result (rplacd list-1 result)
	    list-1 tmp))))

(defun set-exclusive-or (list-1 list-2 &key key (test #'equal) test-not)
  "Return a list of elements that appear in exactly one of LIST-1 and LIST-2."
  (when test-not
    (setq test (complement test-not)))
  (let ((result nil))
    (dolist (element list-1)
      (unless (member (apply-key key element) list-2 :key key :test test)
	(push element result)))
    (dolist (element list-2)
      (unless (member (apply-key key element) list-1 :key key :test test)
	(push element result)))
    result))

(defun nset-exclusive-or (list-1 list-2 &key key (test #'equal) test-not)
  "The destructive version of set-exclusive-or."
  (when test-not
    (setq test (complement test-not)))
  (do* ((head-1 (cons nil list-1))
	(head-2 (cons nil list-2))
	(p-1 head-1))
      ((or (endp (cdr p-1)) (endp (cdr head-2)))
       (progn (rplacd (last p-1) (cdr head-2))
	      (cdr head-1)))
    (do ((p-2 head-2 (cdr p-2)))
	((endp (cdr p-2)) (setq p-1 (cdr p-1)))
      (when (funcall test (apply-key key (cadr p-1)) (apply-key key (cadr p-2)))
	(rplacd p-1 (cddr p-1))
	(rplacd p-2 (cddr p-2))
	(return)))))

(defmacro pushnew (item place &rest keys &environment env)
  "Test if ITEM is the same as any element of the list in PLACE. If not, prepend it to the list, then the new list is stored in PLACE."
  (if (symbolp place)
      `(setq ,place (adjoin ,item ,place ,@keys))
    (multiple-value-bind (temporary-vars values stores setter getter)
	(get-setf-expansion place env)
      (let ((item-var (gensym)))
	`(let* ((,item-var ,item)
		,@(mapcar #'list temporary-vars values)
		(,(car stores) (adjoin ,item-var ,getter ,@keys)))
	   ,setter)))))

(defun rassoc (item alist &key key (test #'equal) test-not)
  "Return the cons in ALIST whose cdr is equal (by TEST) to ITEM."
  (when test-not
    (setq test (complement test-not)))
  (dolist (pair alist nil)
    (when (and pair (funcall test item (apply-key key (cdr pair))))
      (return pair))))

(defun sublis (alist tree &key key (test #'equal) test-not)
  "Substitute data of ALIST for subtrees matching keys of ALIST."
  (when test-not
    (setq test (complement test-not)))
  (labels ((sub (subtree)
		(let ((assoc (assoc (apply-key key subtree) alist :test test)))
		  (cond
		   (assoc (cdr assoc))
		   ((atom subtree) subtree)
		   (t (let ((car (sub (car subtree)))
			    (cdr (sub (cdr subtree))))
			(if (and (eq car (car subtree)) (eq cdr (cdr subtree)))
			    subtree
			  (cons car cdr))))))))
    (sub tree)))

(defun nsublis (alist tree &key key (test #'equal) test-not)
  "Substitute data of ALIST for subtrees matching keys of ALIST destructively."
  (when test-not
    (setq test (complement test-not)))
  (labels ((sub (subtree)
		(let ((assoc (assoc (apply-key key subtree) alist :test test)))
		  (cond
		   (assoc (cdr assoc))
		   ((atom subtree) subtree)
		   (t
		    (rplaca subtree (sub (car subtree)))
		    (rplacd subtree (sub (cdr subtree)))
		    subtree)))))
    (sub tree)))

(defun subst (new old tree &key key (test #'equal) test-not)
  "Substitute NEW for subtrees matching OLD."
  (when test-not
    (setq test (complement test-not)))
  (labels ((sub (subtree)
		(cond
		 ((funcall test old (apply-key key subtree)) new)
		 ((atom subtree) subtree)
		 (t (let ((car (sub (car subtree)))
			  (cdr (sub (cdr subtree))))
		      (if (and (eq car (car subtree)) (eq cdr (cdr subtree)))
			  subtree
			(cons car cdr)))))))
    (sub tree)))

(defun nsubst (new old tree &key key (test #'equal) test-not)
  "Substitute NEW for subtrees matching OLD destructively."
  (when test-not
    (setq test (complement test-not)))
  (labels ((sub (subtree)
		(cond
		 ((funcall test old (apply-key key subtree)) new)
		 ((atom subtree) subtree)
		 (t (rplaca subtree (sub (car subtree)))
		    (rplacd subtree (sub (cdr subtree)))
		    subtree))))
    (sub tree)))

(defun tree-equal (a b &key (test #'equal) test-not)
  "Test whether two trees are of the same shape and have the same leaves."
  (when test-not
    (setq test (complement test-not)))
  (labels ((teq (a b)
		(if (atom a)
		    (and (atom b) (funcall test a b))
		  (and (consp b)
		       (teq (car a) (car b))
		       (teq (cdr a) (cdr b))))))
    (teq a b)))

(defun make-hash-table (&rest args &key (test 'equal))
  (apply #'cl:make-hash-table :test test args))



