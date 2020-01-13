#|
Copyright 2020 Jesse Off <jesseoff@me.com>

Distributed under the MIT license (see LICENSE file)
|#

(defpackage #:ratmath
  (:use #:cl)
  (:export #:rat
           #:infsup
           #:with-interval-math
           #:~
           #:~=
           #:hull
           #:lower
           #:upper
           #:interval
           #:parse-interval
           #:fractions
           #:rat-pipe
           #:farey-pipe
           #:napiers-constant-generator

           #:pipe-first
           #:pipe-cons
           #:pipe-sink
           #:pipe-sink-until
           #:pipe-sink-until-condition
           #:pipe-transform
           #:pipe-append
           #:pipe-end-before
           #:pipe-end-after
           #:pipe-last
           #:pipe-head
           #:pipe-uniq
           #:pipe-mapc
           #:pipe-filter
           #:pipe-signaler
           #:pipe-printer
           #:pipe-apply
           #:pipe-endp
           #:pipe-rest
           #:pipe-to-list
           #:list-to-pipe))
