#|
Copyright 2020 Jesse Off <jesseoff@me.com>

Distributed under the MIT license (see LICENSE file)
|#

(in-package #:ratmath)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro encapsulate (form) `#'(lambda () ,form))

  (defmacro expose (procedure) `(funcall ,procedure))

  (defmacro pipe-cons (object pipe) `(list ,object (encapsulate ,pipe)))

  (defmacro pipe-sink-until-condition (pipe &rest conds)
    "Exposes elements of pipe until one of the condition types in conds is signalled. Returns nil
for end of pipe, or 3 values: #1 being the interrupted pipe, #2 being the condition object, and #3
being the particular condition clause type in the original args that matched."
    (let ((clauses (mapcar (lambda (x) `(,x (c) (values pipe c ',x))) conds))
          (sink-sym (gensym)))
      `(labels ((,sink-sym (pipe)
                  (if (pipe-endp pipe)
                      nil
                      (,sink-sym (handler-case (pipe-rest pipe)
                                   ,@clauses)))))
         (,sink-sym ,pipe)))))

(defun pipe-endp (pipe) (eq pipe :empty-pipe))

(defun pipe-first (pipe) (first pipe))

(defun pipe-rest (pipe)
  "Analogous to the rest function except works on a pipe rather than list"
  (declare (optimize speed (safety 0) (debug 0)))
  (let ((tail (second pipe)))
    (if (functionp tail)
        (setf (second pipe) (expose tail))
        (second pipe))))

(defun pipe-transform (procedure pipe)
  "Runs procedure on each element of pipe; replacing each original element"
  (declare (type function procedure) (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp pipe)
      :empty-pipe
      (pipe-cons (funcall procedure (pipe-first pipe))
                 (pipe-transform procedure (pipe-rest pipe)))))

(defun pipe-sink (pipe)
  "Exposes elements of pipe forever, ignoring the elements. Similar to pipe-mapc with a no-op
procedure.  Useful to provoke the pipeline processing of an infinite pipe."
  (declare (optimize speed (safety 0) (debug 0)))
  (unless (pipe-endp pipe) (pipe-sink (pipe-rest pipe))))

(defun pipe-sink-until (test pipe)
  "Exposes elements of pipe until test returns t. When that happens, returns the (non-empty) pipe.
If the pipe goes empty, returns nil. The test procedure is called with the current element as arg."
  (declare (type function test) (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp pipe)
      :empty-pipe
      (if (funcall test (pipe-first pipe))
          pipe
          (pipe-sink-until test (pipe-rest pipe)))))


(defun pipe-append (pipe1 pipe2)
  "Appends two pipes together"
  (declare (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp pipe1)
      pipe2
      (pipe-cons (pipe-first pipe1)
                 (pipe-append (pipe-rest pipe1)
                              pipe2))))

(defun pipe-end-before (test pipe)
  "Runs test on each element.  When it returns t, the pipe is truncated before that element"
  (declare (type function test) (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp pipe)
      :empty-pipe
      (let ((x (pipe-first pipe)))
        (if (funcall test x)
            :empty-pipe
            (pipe-cons x (pipe-end-before test (pipe-rest pipe)))))))

(defun pipe-end-after (test pipe)
  "Runs test on each element.  When it returns t, the pipe is truncated after that element"
  (declare (type function test) (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp pipe)
      :empty-pipe
      (let ((x (pipe-first pipe)))
        (if (funcall test x)
            (list x :empty-pipe)
            (pipe-cons x (pipe-end-after test (pipe-rest pipe)))))))


(defun pipe-last (pipe &optional (n 1))
  (declare (type (and fixnum (integer 1 *)) n) (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp pipe)
      :empty-pipe
      (let (q)
        (labels ((pipe-last (pipe &aux (next (pipe-rest pipe)))
                   (when (= n (the fixnum (fifo-count q))) (fifo-get! q))
                   (fifo-put! q pipe)
                   (if (pipe-endp next) (fifo-get! q) (pipe-last next))))
          (pipe-last pipe)))))

(defun pipe-head (pipe &optional (n 1))
  "Truncates a pipe after n (default: 1) elements"
  (declare (type fixnum n) (optimize speed (safety 0) (debug 0)))
  (if (or (zerop n) (pipe-endp pipe))
      :empty-pipe
      (pipe-cons (pipe-first pipe) (pipe-head (pipe-rest pipe) (1- n)))))

(defun pipe-to-list (pipe)
  "Returns a list from the given pipe input argument. Infinite recursion results if the pipe is
infinite."
  (declare (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp pipe)
      nil
      (cons (pipe-first pipe) (pipe-to-list (pipe-rest pipe)))))

(defun list-to-pipe (l)
  "Returns a pipe from a list input argument."
  (declare (type list l) (optimize speed (safety 0) (debug 0)))
  (labels ((list-to-pipe (l)
             (if (cdr l)
                 (pipe-cons (car l) (list-to-pipe (cdr l)))
                 (list (car l) :empty-pipe))))
    (if (null l) :empty-pipe (list-to-pipe l))))

(defun pipe-uniq (pipe &optional (pair-uniq-p #'equal) carry)
  "Removes duplicates according to optional predicate func. Only dups in sequence are removed."
  (declare (type function pair-uniq-p) (optimize speed (safety 0) (debug 0)))
  (cond
    ((pipe-endp pipe) (if carry (list carry :empty-pipe) :empty-pipe))
    ((null carry) (pipe-uniq (pipe-rest pipe) pair-uniq-p (pipe-first pipe)))
    ((funcall pair-uniq-p carry (pipe-first pipe))
     (pipe-uniq (pipe-rest pipe) pair-uniq-p (pipe-first pipe)))
    (t (pipe-cons carry
                    (pipe-uniq (pipe-rest pipe) pair-uniq-p (pipe-first pipe))))))

(defun pipe-mapc (procedure pipe)
  "Runs function on each element.  Returns nothing."
  (declare (type function procedure) (optimize speed (safety 0) (debug 0)))
  (unless (pipe-endp pipe)
    (funcall procedure (pipe-first pipe))
    (pipe-mapc procedure (pipe-rest pipe))))

(defun pipe-filter (procedure pipe)
  "If procedure returns t, that particular pipe element is removed from the sequence."
  (declare (type function procedure) (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp pipe)
      :empty-pipe
      (let* ((x (pipe-first pipe)) (ret (funcall procedure x)))
        (if ret
            (pipe-filter procedure (pipe-rest pipe))
            (pipe-cons x (pipe-filter procedure (pipe-rest pipe)))))))


(defun pipe-signaler (pipe)
  "For each condition object in pipe, set up some useful restarts and signal it.  If nothing
handles it, the default behavior is to ignore.  If the use-value restart is invoked, that value will
be returned as a pipe datum element."
  (declare (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp pipe)
      :empty-pipe
      (let ((x (pipe-first pipe)))
        (if (subtypep (type-of x) 'condition)
            (let ((sigret (restart-case (signal x)
                            (use-value (v) v)
                            (continue () nil))))
              (if sigret
                  (pipe-cons sigret (pipe-signaler (pipe-rest pipe)))
                  (pipe-signaler (pipe-rest pipe))))
            (pipe-cons x (pipe-signaler (pipe-rest pipe)))))))

(defun pipe-printer (pipe)
  (pipe-mapc #'print pipe))

(defun pipe-apply (procedure pipe)
  "Runs procedure on every element as they are exposed, but does not transform the element."
  (declare (type function procedure) (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp pipe)
      :empty-pipe
      (pipe-cons (let ((x (pipe-first pipe))) (funcall procedure x) x)
                 (pipe-apply procedure (pipe-rest pipe)))))

