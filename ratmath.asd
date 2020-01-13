#|
Copyright 2020 Jesse Off <jesseoff@me.com>

Distributed under the MIT license (see LICENSE file)
|#

(asdf:defsystem #:ratmath
  :description "Math utilities for working with rational numbers and intervals."
  :author "Jesse Off <jesseoff@me.com>"
  :license  "MIT"
  :version "1"
  :serial t
  :components ((:file "package")
               (:file "fifo")
               (:file "pipe")
               (:file "ratmath")))
