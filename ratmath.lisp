#|
Copyright 2020 Jesse Off <jesseoff@me.com>

Distributed under the MIT license (see LICENSE file)
|#

(in-package #:ratmath)

(defun my/ (a b)
  (declare (type (or null integer) a)
           (type integer b))
  (if (or (not a) (zerop b))
      nil
      (let ((r (floor a b))) r)))

(defun my- (a b)
  (declare (type (or null integer) a)
           (type integer b))
  (if a (- a b) nil))

(defun my-min (&rest rest)
  (labels
      ((my-min (args &optional cur)
         (declare (type list args) (type (or null integer) cur))
         (if (endp args)
             cur
             (let ((n (car args)))
               (declare (type (or null integer) n))
               (if (or (not (integerp n))
                       (and (integerp cur)
                            (> n cur)))
                   (my-min (cdr args) cur)
                   (my-min (cdr args) n))))))
    (declare (ftype (function (list &optional integer) (or null integer)) my-min) (optimize speed))
    (my-min rest)))

(defun napiers-constant-generator ()
  "Returns an infinite/irrational continued fraction expansion of Euler's number 'e'"
  (labels
      ((euler-3more (n)
         (list 1 (list 1 (list (* n 2) (encapsulate (euler-3more (1+ n))))))))
    (list 2 (list 1 (list 2 (encapsulate (euler-3more 2)))))))

(defun rationalize-continued-fraction-pipe (generator-pipe)
  "The normal continued-fraction-pipes have each term annotated with a lexical closure that returns
the remainder to the terminal value. This value is used to qualify visiting iffy semi-convergents in
a denominator/numerator limited rational approximation. With irrational numbers there is no
end-value so we can give downpipe logic no insight as to whether an iffy semi-convergent is worthy."
  (pipe-transform (lambda (x)
                      (declare (type integer x))
                      (cons x (constantly 0))) generator-pipe))

(defun truncate-within-interval (cf1 cf2)
  "Takes 2 continued-fraction-pipes and returns one that stops at the simplest rational inbetween"
  (declare (optimize speed (safety 0) (debug 0)))
  (if (or (pipe-endp cf1) (pipe-endp cf2))
      :empty-pipe
      (let* ((a (pipe-first cf1))
             (b (pipe-first cf2))
             (an (car a))
             (bn (car b)))
        (declare (type integer an bn))
        (if (/= an bn)
            (list (cons (1+ (min an bn)) (constantly 0))  :empty-pipe)
            (pipe-cons a (truncate-within-interval (pipe-rest cf1) (pipe-rest cf2)))))))

(defun continued-fraction-pipe (f)
  "Returns a pipe of continued fraction terms from the input rational arg."
  (declare (type rational f) (optimize speed (safety 0) (debug 0)))
  (multiple-value-bind (q r) (floor f)
    (declare (type integer q) (type rational r))
    (if (zerop r)
        (list (cons q (constantly 0)) :empty-pipe)
        (pipe-cons (cons q (encapsulate (rem (numerator r) (denominator r))))
                     (continued-fraction-pipe (/ r))))))

(defstruct
    (convergent
     (:constructor make-convergent (cf r0 r1 a &optional (q-offset 0)))
     (:constructor make-semi-convergent (q-offset c &aux (cf (convergent-cf c))
                                                      (r0 (convergent-r0 c))
                                                      (r1 (convergent-r1 c))
                                                      (a (convergent-a c)))))
  "Represents a (semi-)convergent in the rational approximation of a continued fraction."
  cf r0 r1 (q-offset 0 :type integer) a rat)

(defstruct
    (stern-brocot
     (:constructor make-stern-brocot (left-parent right-parent)))
  "Stern-Brocot left/right parent used to address a node in the Stern-Brocot fraction tree."
  left-parent right-parent)

(defun semi-convergent-p (c)
  "Semi-convergents are convergents with a truncated (up to 1/2) CF term"
  (not (zerop (convergent-q-offset c))))

(defun semi-convergent-iffy-p (c)
  "Iffy semi-convergents are the exactly 1/2 CF semi-convergent of even terms."
  (= (convergent-q c) (* -2 (convergent-q-offset c))))

(defun convergent-numerator (c)
  (declare (type convergent c))
  (car (convergent-fract c)))

(defun convergent-denominator (c)
  (declare (type convergent c))
  (cdr (convergent-fract c)))

(defun convergent-q (c)
  (declare (type convergent c))
  (car (convergent-cf c)))

(defun convergent-fract (c)
  (declare (type convergent c))
  (if (convergent-rat c)
      (convergent-rat c)
      (let ((q (convergent-q c))
            (r0n (car (convergent-r0 c)))
            (r1n (car (convergent-r1 c)))
            (r0d (cdr (convergent-r0 c)))
            (r1d (cdr (convergent-r1 c)))
            (qo (convergent-q-offset c)))
        (declare (type integer q r0n r1n r0d r1d qo))
        (setf (convergent-rat c) (cons (+ r1n (* (+ q qo) r0n)) (+ r1d (* (+ q qo) r0d)))))))

(defun convergent-equal (a b)
  (declare (type convergent a b))
  (equal (convergent-fract a) (convergent-fract b)))

(defun convergent-ratio (c &aux (f (convergent-fract c)))
  (declare (type convergent c) (type cons f))
  (/ (car f) (cdr f)))

(defun convergent-stern-brocot (c)
  "From a convergent struct, make a Stern-Brocot struct by calculating the left and right parents"
  (if (not (convergent-p c)) (make-stern-brocot '(1 . 0) '(0 . 0))
      (let ((lr (> (* (car (convergent-r0 c)) (cdr (convergent-r1 c)))
                   (* (car (convergent-r1 c)) (cdr (convergent-r0 c)))))
            (x (cons (- (convergent-numerator c) (car (convergent-r0 c)))
                     (- (convergent-denominator c) (cdr (convergent-r0 c))))))
        (if lr
            (make-stern-brocot (convergent-r0 c) x)
            (make-stern-brocot x (convergent-r0 c))))))

(defun stern-brocot-numerator (sb)
  (declare (type stern-brocot sb))
  (+ (car (stern-brocot-left-parent sb)) (car (stern-brocot-right-parent sb))))

(defun stern-brocot-denominator (sb)
  (declare (type stern-brocot sb))
  (+ (cdr (stern-brocot-left-parent sb)) (cdr (stern-brocot-right-parent sb))))

(defun stern-brocot-fract (sb)
  (declare (type stern-brocot sb))
  (cons (stern-brocot-numerator sb) (stern-brocot-denominator sb)))

(defun stern-brocot-ratio (sb)
  (declare (type stern-brocot sb))
  (let ((f (stern-brocot-fract sb)))
    (/ (car f) (cdr f))))

(defun calc-stern-brocot (n)
  (declare (type real n))
  (convergent-stern-brocot (best-convergent (continued-fraction-pipe (rational n)))))

(defmethod print-object ((obj convergent) stream)
  (print-unreadable-object (obj stream :type t)
    (let ((f (convergent-fract obj)))
      (format stream "~a/~a" (car f) (cdr f)))))

(defun semi-convergent-closest-to-lim (cv limn limd &aux (q (convergent-q cv)))
  "From a specific convergent, check semi-convergents for one below num/denom limits"
  (declare (type (or null (integer 1 *)) limn limd)
           (type integer q)
           (type convergent cv)
           (optimize speed (safety 0) (debug 0)))
  (labels
      ((halfq-is-ok-p (cv)
         (let ((a-1 (expose (convergent-a cv)))
               (a0 (expose (cdr (convergent-cf cv))))
               (d-1 (cdr (convergent-r0 cv)))
               (d-2 (cdr (convergent-r1 cv))))
           (declare (type integer a-1 a0 d-1 d-2))
           (> (* d-2 a-1) (* a0 d-1)))))
    (let ((nqo (my- (my-min
                     (my/ (my- limd (cdr (convergent-r1 cv))) (cdr (convergent-r0 cv)))
                     (my/ (my- limn (car (convergent-r1 cv))) (car (convergent-r0 cv))))
                    q))
          (fqo (if (<= q 1) 0 (- (ceiling (1+ q) 2) q))))
      (cond
        ((or (not nqo) (>= nqo 0)) cv)
        ((>= nqo fqo) (make-semi-convergent nqo cv))
        ((and (evenp q) (halfq-is-ok-p cv)) (make-semi-convergent (1- fqo) cv))
        (t (make-semi-convergent fqo cv))))))

(defun convergents-pipe (cfs &optional (r0 '(1 . 0)) (r1 '(0 . 1)) (a (constantly 0)))
  "From a continued-fraction-pipe return a pipe of the resultant convergents."
  (declare (type cons r0 r1) (type function a) (optimize speed (safety 0) (debug 0)))
  (if (pipe-endp cfs)
      :empty-pipe
      (let ((x (make-convergent (pipe-first cfs) r0 r1 a))
            (nexta (cdr (pipe-first cfs))))
        (declare (type convergent x))
        (pipe-cons x (convergents-pipe (pipe-rest cfs) (convergent-fract x) r0 nexta)))))

(defmacro best-convergent-test-fn (&rest args)
  (destructuring-bind (&key limn limd &allow-other-keys) args
    (let ((n `(> (the integer (convergent-numerator cv)) ,limn))
          (d `(> (the integer (convergent-denominator cv)) ,limd)))
      `(lambda (cv)
         (declare (optimize speed (safety 0) (debug 0)) (type convergent cv))
         ,@(cond
             ((and (null limn) (null limd)) `((declare (ignore cv)) nil))
             ((and (null limn) limd) `(,d))
             ((and limn (null limd)) `(,n))
             (t `((or ,d ,n))))))))

(defun best-convergent (arg &key limn limd test-fn)
  "From a rationalized continued-fraction-pipe arg, returns best convergent honoring limits.
2nd value being the next best ignoring limits."
  (declare (type (or null (integer 1 *)) limn limd) (optimize speed (safety 0) (debug 0)))
  (labels
      ((get-end-p ()
         (cond
           (test-fn test-fn)
           ((and limn limd) (best-convergent-test-fn :limd limd :limn limn))
           (limd (best-convergent-test-fn :limd limd))
           (limn (best-convergent-test-fn :limn limn))
           (t (best-convergent-test-fn))))
       (semi-convergents (cvs lim-test-p &optional prev)
         (declare (type (function (convergent) boolean) lim-test-p)
                  (optimize speed (safety 0) (debug 0)))
         (cond
           ((pipe-endp cvs) (list prev))
           ((funcall lim-test-p (pipe-first cvs))
            (let ((sc (semi-convergent-closest-to-lim (pipe-first cvs) limn limd)))
              (cond ((funcall lim-test-p sc) (list prev sc))
                    ((last-semi-convergent-p sc) (semi-convergents (pipe-rest cvs) lim-test-p sc))
                    (t (list sc (next-semi-convergent sc))))))
           (t (semi-convergents (pipe-rest cvs) lim-test-p (pipe-first cvs)))))
       (next-semi-convergent (c) (make-semi-convergent (1+ (convergent-q-offset c)) c))
       (last-semi-convergent-p (c) (zerop (convergent-q-offset c))))
    (declare (inline last-semi-convergent-p next-semi-convergent get-end-p)
             (ftype (function (convergent) convergent) next-semi-convergent)
             (ftype (function (convergent) boolean) last-semi-convergent-p))
    (values-list (semi-convergents (convergents-pipe arg) (get-end-p)))))

(let ((cf0 (list (cons 0 (constantly 0)) :empty-pipe)))
  (defun farey-pipe (order &key test-fn (from-cf cf0) (limn order))
    "Returns a farey sequence; 2nd value is an encapsulated reverse sequence"
    (declare (type (integer 1 *) order) (type (or null (integer 1 *)) limn)
             (optimize speed (safety 0) (debug 0)))
    (labels
        ((farey (x dir)
           (declare (type boolean dir) (type stern-brocot x))
           (if (zerop (stern-brocot-numerator x))
               (if dir
                   :empty-pipe
                   (let ((yr (/ 1 order))) (pipe-cons yr (farey (calc-stern-brocot yr) dir))))
               (let* ((l (if dir (stern-brocot-right-parent x) (stern-brocot-left-parent x)))
                      (k (my-min (my/ (my- limn (car l)) (stern-brocot-numerator x))
                                 (my/ (my- order (cdr l)) (stern-brocot-denominator x))))
                      (y (cons (+ (* (stern-brocot-numerator x) k) (car l))
                               (+ (* (stern-brocot-denominator x) k) (cdr l)))))
                 (cond
                   ((or (zerop (cdr y)) (zerop (car y))) :empty-pipe)
                   (t (let ((yr (/ (car y) (cdr y))))
                        (pipe-cons yr (farey (calc-stern-brocot yr) dir))))))))
         (farey-start (a b dir)
           (if (and b (eq (< (convergent-ratio a) (convergent-ratio b)) (and t dir)))
               (pipe-cons (convergent-ratio a) (farey (convergent-stern-brocot a) dir))
               (farey (convergent-stern-brocot a) dir))))
      (multiple-value-bind (a b) (best-convergent from-cf :limd order :limn limn :test-fn test-fn)
        (values (farey-start a b nil) (encapsulate (farey-start a b t)))))))

(defun infsup-limd (arg &key limd limn test-fn open)
  "Returns an infimum/supremum interval; 2nd value is alpha (>.5 when supremum is closer)"
  (declare (type (integer 1 *) limd)
           (type (or null (integer 1 *)) limn)
           (type rational arg))
  (if (and (not open)
           (or (not limd) (>= limd (denominator arg)))
           (or (not limn) (>= limn (numerator arg))))
      arg
      (multiple-value-bind (fwd rev)
          (farey-pipe limd :from-cf (continued-fraction-pipe arg) :limn limn :test-fn test-fn)
        (let ((f (if (pipe-endp fwd) 'inf (pipe-first fwd)))
              (rev (expose rev)))
          (let ((r (if (pipe-endp rev) 0 (pipe-first rev))))
            (values (cons r f) (/ (- arg r) (- f r))))))))

(defun fractions (arg &key (order 2))
  "Prints out rational approximations, one per line, with the PPM or PPB error."
  (labels
      ((ppm (x)
         (if (< (abs x) 1/1000000)
             (format nil "~,3e PPB" (coerce (* x 1000000000) 'double-float))
             (format nil "~,3f PPM" (coerce (* x 1000000) 'double-float))))
       (verilog (num) (format nil "~a'd~a" (integer-length num) num))
       (print-fract (x)
         (format t "~%~a/~a ~a" (verilog (numerator x))
                 (verilog (denominator x)) (ppm (/ (- (rational arg) x) (rational arg))))))
    (pipe-mapc #'print-fract (rat-pipe arg order))))


(defun rat-pipe (arg &optional (mult 2))
  "Returns a pipe of best rational approximations for every power-of-mult numerator/denominator.  If
arg is not a number, assumes it is a continued fraction pipe."
  (declare (type (and fixnum (integer 2 *)) mult) (optimize speed (safety 0) (debug 0)))
  (labels
       ((expt-convergents (cvs &optional (limn 1) (limd 1))
         (declare (type (integer 1 *) limn limd))
         (cond
           ((pipe-endp cvs) :empty-pipe)
           ((and limd (> (convergent-denominator (pipe-first cvs)) limd))
            (let ((sc (semi-convergent-closest-to-lim (pipe-first cvs) limn limd))
                  (next-limd (1- (* mult (1+ limd)))))
              (if (<= (convergent-denominator sc) limd)
                  (pipe-cons sc (expt-convergents cvs limn next-limd))
                  (expt-convergents cvs limn next-limd))))
           ((and limn (> (convergent-numerator (pipe-first cvs)) limn))
            (let ((sc (semi-convergent-closest-to-lim (pipe-first cvs) limn limd))
                  (next-limn (1- (* mult (1+ limn)))))
              (if (<= (convergent-numerator sc) limn)
                  (pipe-cons sc (expt-convergents cvs next-limn limd))
                  (expt-convergents cvs next-limn limd))))
           (t (pipe-cons (pipe-first cvs)
                         (expt-convergents (pipe-rest cvs) limn limd)))))
       (convergents-of-equal-binary-order-p (cva cvb)
         (and (= (integer-length (convergent-numerator cva))
                 (integer-length (convergent-numerator cvb)))
              (= (integer-length (convergent-denominator cva))
                 (integer-length (convergent-denominator cvb)))))
       (convergents-of-equal-order-p (cva cvb)
         (and (= (floor (log (1+ (convergent-numerator cva)) mult))
                 (floor (log (1+ (convergent-numerator cvb)) mult)))
              (= (floor (log (convergent-denominator cva) mult))
                 (floor (log (convergent-denominator cvb) mult))))))
    (pipe-transform #'convergent-ratio
                    (pipe-uniq
                     (expt-convergents
                      (convergents-pipe
                       (if (realp arg)
                           (continued-fraction-pipe (rational arg))
                           (rationalize-continued-fraction-pipe arg))))
                     (if (= mult 2)
                         #'convergents-of-equal-binary-order-p
                         #'convergents-of-equal-order-p)))))

(defun infsup-tol (x abstol &optional tol)
  "Returns an infimum/supremum interval given a tolerance."
  (cond
    ((and (null tol) (null abstol)) x)
    ((realp tol) (infsup-tol x abstol (cons tol tol)))
    ((realp abstol) (infsup-tol x (cons abstol abstol) tol))
    ((consp tol) (let ((l (* (car tol) x))
                       (u (* (cdr tol) x)))
                   (if (consp abstol)
                       (infsup-tol x (cons (min (car abstol) l) (min (cdr abstol) u)))
                       (infsup-tol x (cons l u)))))
    ((and (zerop (car abstol)) (zerop (cdr abstol)) x))
    (t (cons (- x (car abstol)) (+ x (cdr abstol))))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun functionalp (fn &optional args)
    (and (symbolp fn)
         (fboundp fn)
         (not (and (eq '~ fn) (member :random args)))
         (not (or (special-operator-p fn)
                  (eq 'setf fn)
                  (search "!" (symbol-name fn))))))

  (defun eval-constants (args &optional (pure-function-symbolp #'functionalp))
    (labels
        ((eval-constant (x)
           (if (and (consp x) (funcall pure-function-symbolp (car x) (cdr x)))
               (if (every #'constantp (cdr x))
                   `(quote ,(eval x))
                   (eval-constants x pure-function-symbolp))
               x)))
      (let ((x (mapcar #'eval-constant args)))
        (if (equal args x)
            (values args (every #'constantp args))
            (eval-constants x pure-function-symbolp))))))

(defun lower (x)
  "Returns the lower limit of an interval"
  (if (consp x) (car x) x))

(defun upper (x)
  "Returns the upper limit of an interval"
  (if (consp x) (cdr x) x))

(defun interval (l u)
  "Constructs an interval from the given lower/upper bounds"
  (if (= l u) l (cons l u)))

(defun %infsup (x &key limn limd tol abstol open test-fn)
  (declare (type (or null (integer 1 *)) limn limd))
  (labels
      ((%%infsup (x)
         (cond
           ((stringp x) (or (parse-interval x) x))
           ((or (realp x) (and (consp x) (realp (cdr x)))) (%infsup x tol abstol))
           ((listp x) (mapcar #'%%infsup x))
           (t x)))
       (%infsup (x &optional tol abstol)
         (cond
           ((consp x) (interval (lower (%infsup (car x))) (upper (%infsup (cdr x)))))
           ((or tol abstol) (%infsup (infsup-tol x abstol tol)))
           ((or limd limn) (infsup-limd (rationalize x)
                                        :open open :limd limd :limn limn :test-fn test-fn))
           (t x))))
    (%%infsup x)))

(defmacro infsup (&rest args)
  "Returns infimum/supremum intervals. All strings and numbers in tree are converted keeping
everything else intact. Exacts are fuzzified according to :tol and :abstol first, and then
potentially widened further with :limd and :limn, which performs a rational approximation. Intervals
already present in the structure, whether by explicit cons or via a string, will not be fuzzified
further by :abstol and :tol, but they may be widened if rational approximation is called out via
:limd/:limn args. Exact rationals will only convert to intervals if 1) their numerators/denominators
exceed :limn/:limd or 2) an :open t arg is given. When the arg is an exact and rational
approximation is called out, a 2nd value, alpha, is returned which is a number from 0-1 representing
the location of the original exact in the returned interval."
  (let ((gs (gensym))
        (rargs (multiple-value-list (eval-constants args))))
    (destructuring-bind (&key limn limd &allow-other-keys) (cdar rargs)
      (cond
        ((cadr rargs) 
         `(values-list (quote ,(eval `(multiple-value-list
                                       (%infsup ,@(car rargs)))))))
        ((and limd (constantp limd) (constantp limn))
         `(let ((,gs (best-convergent-test-fn ,@(cdar rargs))))
            (%infsup ,@(car rargs) :test-fn ,gs)))
        (t `(%infsup ,@(car rargs)))))))

(defun %rat (x &key limn limd test-fn)
  (declare (type (or null (integer 1 *)) limn limd)
           (type (or cons real string) x))
  (let ((xx (if (stringp x) (parse-interval x) x)))
    (convergent-ratio (best-convergent (if (consp xx)
                                           (truncate-within-interval
                                            (continued-fraction-pipe (rational (car xx)))
                                            (continued-fraction-pipe (rational (cdr xx))))
                                           (continued-fraction-pipe (rational xx)))
                                       :limn limn
                                       :limd limd
                                       :test-fn test-fn))))

;; Most of the work is done in %rat. The macro form attempts to collapse all constants down early
;; and instantiates a static helper function if the :limd and :limn are constant but the
;; number/interval arg isn't.
(defmacro rat (&rest args)
  "Performs a rational approximation of an exact number or interval. Takes keyword args :limn and
:limd to represent max numerator and max denominator. Also will parse numeric strings into intervals
ala parse-interval.  Always returns an exact (i.e. not another interval)."
  (let ((gs (gensym))
        (rargs (multiple-value-list (eval-constants args))))
    (destructuring-bind (x &key limn limd &allow-other-keys) (car rargs)
      (cond
        ((cadr rargs) `(quote ,(eval `(%rat ,@(car rargs)))))
        ((and limd (constantp limd) (constantp limn))
         `(let ((,gs (best-convergent-test-fn ,@(cdar rargs))))
            (%rat ,x ,@(cdar rargs) :test-fn ,gs)))
        (t `(%rat ,@(car rargs)))))))

(defun hull (&rest args)
  "Takes exacts and intervals as arguments and returns an interval enclosure containing the
min/max.  If the range between min and max is 0, hull will return an exact."
  (labels
      ((hull (l lower upper)
         (cond
           ((endp l) (interval lower upper))
           ((numberp (car l)) (hull (cdr l)
                                    (if (< (car l) lower) (car l) lower)
                                    (if (> (car l) upper) (car l) upper)))
           (t (hull (cdr l)
                    (if (< (caar l) lower) (caar l) lower)
                    (if (> (cdar l) upper) (cdar l) upper))))))
    (hull (cdr args) (lower (car args)) (upper (car args)))))

(defun interval+ (&rest args)
  (reduce (lambda (a b)
            (if (realp a)
                (if (realp b)
                    (+ a b)
                    (cons (+ a (car b)) (+ a (cdr b))))
                (if (realp b)
                    (cons (+ (car a) b) (+ (cdr a) b))
                    (cons (+ (car a) (car b)) (+ (cdr a) (cdr b))))))
          args
          :initial-value 0))

(defun interval- (&rest args)
  (labels
      ((neg (a)
         (if (realp a)
             (- a)
             (let ((x (- (car a))) (y (- (cdr a))))
               (if (< x y)
                   (cons x y)
                   (cons y x))))))
    (if (cdr args)
        (apply #'interval+ (car args) (mapcar #'neg (cdr args)))
        (neg (car args)))))

(defun interval* (&rest args)
  (labels
      ((iv (&rest n) (apply #'hull n))
       (mults (a b)
         (if (realp a)
             (if (realp b)
                 (* a b)
                 (iv (* a (car b)) (* a (cdr b))))
             (if (realp b)
                 (iv (* (car a) b) (* (cdr a) b))
                 (iv (* (car a) (car b)) (* (car a) (cdr b))
                     (* (cdr a) (cdr b)) (* (cdr a) (car b)))))))
    (reduce #'mults
            args
            :initial-value 1)))

(defun interval/ (&rest args)
  (labels
      ((recip (a) (if (realp a) (/ a) (cons (/ (car a)) (/ (cdr a)))))
       (recip-zerocheck (a) (if (~= 0 a) (error 'division-by-zero) (recip a))))
    (if (cdr args)
        (apply #'interval* (car args) (mapcar #'recip-zerocheck (cdr args)))
        (recip (car args)))))

(defun intervalexpt (x y)
  (labels
      ((pow (x n)
         (cond
           ((or (and (integerp n) (oddp n)) (>= (lower x) 0))
            (cons (expt (lower x) n) (expt (upper x) n)))
           ((< (upper x) 0)
            (cons (expt (upper x) n) (expt (lower x) n)))
           (t (cons 0 (max (expt (upper x) n) (expt (lower x) n)))))))
    (cond
      ((consp y) (hull (intervalexpt x (lower y)) (intervalexpt x (upper y))))
      ((consp x) (pow x y))
      (t (expt x y)))))

(defun intervalexp (x) (hull (exp (lower x)) (exp (upper x))))

(defun intervallog (x &optional n)
  (cond
    ((and (null n) (numberp x)) (log x))
    ((and (numberp n) (numberp x)) (log x n))
    ((and (numberp n) (consp x)) (hull (log (upper x) n) (log (lower x) n)))
    ((and (consp n) (consp x)) (hull (log (upper x) (lower n))
                                     (log (lower x) (lower n))
                                     (log (upper x) (upper n))
                                     (log (lower x) (upper n))))
    (t (hull (log (upper x)) (log (lower x))))))

(defun intervalsqrt (x) (hull (sqrt (upper x)) (sqrt (lower x))))

(defun intervalabs (x) (hull (abs (upper x)) (abs (lower x))))

(defmacro interval~ (&rest args)
  "When the ~ function is encounted within a with-interval-math block, it converts exacts to
intervals. Outside of the lexical scope of a with-interval-math block, ~ converts intervals into
exacts."
  `(infsup ,@args))

(defun ~ (&rest args)
  "Converts intervals into an exacts. :random picks a random value within the interval instead of
the midpoint. :rat picks the first convergent rational fraction (which may not be the midpoint)
:upper or :lower selects the upper or lower limit. :alpha modifies whats considered the midpoint of
the interval. :discrete requests to only return one of either the lower or upper interval limit. By
default, returns the midpoint. If passed in a list/tree, recursively modifies everything that looks
like an interval and leaves everything else intact."
  (destructuring-bind (arg &key random rat upper lower (alpha 1/2) discrete) args
    (cond
      ((and (consp arg) (listp (cdr arg)))
       (mapcar (lambda (x) (apply #'~ x (cdr args))) arg))
      ((not (and (consp arg) (realp (car arg)) (realp (cdr arg)))) arg)
      (random (~ arg
                 :discrete discrete
                 :alpha (if (= (random 2) 1)
                            (+ alpha (* (- 1 alpha) (random 1.0)))
                            (* alpha (random 1.0)))))
      ((or upper (and discrete (>= alpha 1/2))) (upper arg))
      ((or lower (and discrete (< alpha 1/2))) (lower arg))
      (rat (rat arg))
      (t (let ((lo (lower arg))) (+ lo (* alpha (- (upper arg) lo))))))))

(defun ~= (a b)
  "Compares either exacts or intervals for possible equality."
  (or
   (equal a b)
   (let ((la (lower a))
         (ua (upper a))
         (lb (lower b))
         (ub (upper b)))
     (or (<= lb la ub)
         (<= lb ua ub)
         (<= la lb ua)
         (<= la ub ua)))))

(defun parse-interval (s)
  "Turns strings of rationals or floats into rational intervals. Infers interval radius from number
specification. e.g. 1.000 implies an interval of [.9995, 1.0005) whereas just 1 implies [.5, 1.5).
Exponent notation is also recognized; 1e3 is [500, 1500) whereas 1000 is [999.5, 1000.5). A rational
specified as 22/7 is converted as (43/14, 45/14)."
  (declare (optimize speed (safety 0) (debug 0)))
  (cond
    ((listp s) (mapcar #'parse-interval s))
    ((not (stringp s)) s)
    (t (let ((n 0) (d 1) neg neg-exp (e 0))
         (declare (type (integer 0 *) d e n) (type boolean neg neg-exp))
         (labels
             ((digit-val (c) (position c "0123456789"))
              (exp-digit-p (c) (find (char-downcase c) "esdfl"))
              (initial (c)
                (case c
                  (#\~ #'initial1)
                  (#\- (setf neg t) #'gen-num0)
                  (#\+ #'gen-num0)
                  (t (gen-num0 c))))
              (initial1 (c)
                (case c
                  (#\- (setf neg t) #'gen-num0)
                  (#\+ #'gen-num0)
                  (t (gen-num0 c))))
              (gen-num0 (c)
                (unless (digit-char-p c) (return-from parse-interval nil))
                (setf n (digit-val c))
                #'gen-num)
              (gen-num (c)
                (cond
                  ((digit-char-p c)
                   (setf n (+ (digit-val c) (* 10 n)))
                   #'gen-num)
                  ((char-equal c #\.) #'gen-num-post-pt)
                  ((char-equal c #\/) #'gen-denom0)
                  ((exp-digit-p c) #'gen-exp-?neg)
                  (t (return-from parse-interval nil))))
              (gen-num-post-pt (c)
                (if (exp-digit-p c)
                    #'gen-exp-?neg
                    (progn
                      (unless (digit-char-p c) (return-from parse-interval nil))
                      (setf n (+ (digit-val c) (* 10 n)))
                      (setf d (* d 10))
                      #'gen-num-post-pt)))
              (gen-denom0 (c)
                (unless (digit-char-p c) (return-from parse-interval nil))
                (setf d (digit-val c))
                #'gen-denom)
              (gen-denom (c)
                (unless (digit-char-p c) (return-from parse-interval nil))
                (setf d (+ (digit-val c) (* 10 d)))
                #'gen-denom)
              (gen-exp-?neg (c)
                (case c
                  (#\- (setf neg-exp t) #'gen-exp)
                  (#\+ #'gen-exp)
                  (t (gen-exp c))))
              (gen-exp (c)
                (unless (digit-char-p c) (return-from parse-interval nil))
                (setf e (+ (digit-val c) (* 10 e)))
                #'gen-exp))
           (declare (type string s))
           (let ((state #'initial))
             (declare (type (function (character) function) state))
             (dotimes (i (length s)) (setf state (funcall state (char s i))))
             (when (not (member state (list #'gen-num #'gen-denom #'gen-exp #'gen-num-post-pt)))
               (return-from parse-interval nil))
             (let ((x (/ n d)))
               (declare (type rational x))
               (when neg (setf x (- x)))
               (interval* (expt 10 (if neg-exp (- e) e))
                          (interval~ x :abstol (/ (* 2 d)))))))))))

(defmacro with-interval-math (&rest body)
  "Replaces arithmetic calls like *-/+ with interval*-/+ and turns ~##.## symbols into literal
rational intervals with implied precision based on the number of digits after the decimal point. (as
in parse-interval)"
  (labels
      ((patch-form (a)
         (cond
           ((interval-symbol-p a) (replace-approximant a))
           ((not (listp a)) a)
           ((symbolp (car a))
            (let ((isym (find-symbol (concatenate 'string "INTERVAL" (symbol-name (car a)))
                                     (symbol-package 'with-interval-math))))
              (cons (if isym isym (car a)) (mapcar #'patch-form (cdr a)))))
           (t a)))
       (interval-symbol-p (s) (and (symbolp s) (char= #\~ (char (symbol-name s) 0))))
       (replace-approximant (x)
         (let ((iv (parse-interval (symbol-name x))))
           (when (null iv) (error "Bad interval literal symbol ~a" x))
           (unintern x)
           `(quote ,iv))))
    (let ((b (mapcar #'patch-form body)))
      (if (cdr b)
          (eval-constants `(progn ,@b))
          (car (eval-constants b))))))
