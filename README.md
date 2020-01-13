# Ratmath

Ratmath is a collection of utilities for working with rational numbers,
approximations, and intervals in Common Lisp. Functions are included to
calculate the closest single approximant given a maximum numerator/denominator
(`rat`) or the smallest bounded rational interval (`infsup`). The `infsup`
function can find the floating point constant _pi_ with a denominator limit of,
e.g. 256, to be within the interval 688/219 to 355/113, and the
`with-interval-math` function can use this interval instead of exact values to
carry out further interval arithmetic to yield interval results.

## A Better `(rational NUM)` and `(rationalize NUM)` Function
In its simplest use case, it is an extension of Common Lisp's _rationlize_ that can
take keyword arguments :limd and :limn representing the maximum numerator/denominator:

    CL-USER> (ratmath:rat pi :limd 255)
    355/113

## Calculating Rational Intervals

Interval arithmetic is a powerful and convenient way of doing calculations in
engineering but is seldom accomodated in the base functionality of computer
languages. [Wikipedia](https://en.wikipedia.org/wiki/Interval_arithmetic)

There are other libraries for interval math using floats, but this library
instead uses rationals, a numerical data type not commonly appreciated as a base
numerical type amongst the other languages. With Common Lisp's built-in infinite
size integers, there is no limit to the precision of rational numbers which
simplifies a lot of the inherent complexity of writing floating point interval
libraries which have to worry about round off on every operation.

The disadvantage of using rationals rather than floats is that some calculations
can end up generating extremely large numerators and denominators quickly.
Conveniently, these large numbers can be rationally approximated into intervals
of smaller numbers at any time in the middle or at the end of a calculation. As
as example, the number representing e * pi using high precision rational constants
on _e_ and _pi_ yields a rational result which has 72-bit numerator (which would
cause overflow in anything other than Common Lisp). This bignum rational could be
reduced to the following 16-bit rational interval with ratmath:


    CL-USER> (* (rational pi) (rational (exp 1.0)))
    2520484590068807905375/295147905179352825856
    CL-USER> (ratmath:infsup * :limd 65535 :limn 65535)
    (23749/2781 . 50077/5864)
    32894771015794204823/36893488147419103232

You can usually ignore the second value returned from `infsup`. It represents an
_alpha_, or a number between 0 and 1 representing the location of the original
number inside the returned interval. The _alpha_ calculation returns a rational
that may be of higher order than even the original rational.  For most cases, it
would be recommended to coerce this rational into a float or use the `rat` function
to reduce its precision.

## Approximations From Rational Intervals

There are routines to work in reverse as well. That is, to go from an interval
to the simplest rational number within that interval. The Common Lisp builtin
`rational` differs only from its cousin `rationalize` by calculating a rational
approximation from an interval about the original floating point number equal to
the epsilon of the floating point representation. Here's how you do something
similar, but with an explicitly bounded interval with *ratmath*:

    CL-USER> (ratmath:rat '(110/333 . 221/333))
    1/2

## Trivial Interval Arithmetic

Intervals can be useful outside of rational approximation and used in the
general arithmetic of non-exact measurements and numbers. For instance, on a
calculation returning voltage measurements of an analog input, one usually needs
to plug in numbers representing the voltage reference and any input resistor
divider ratios. Using exact numbers for these is suboptimal as the truth is that
these specifications are fuzzy and have non-zero tolerances. Interval math can
be used instead to output an _interval_ representing where the analog input true
value might actually be between.

An interval at its core is simply a cons of two numbers. e.g. `'(99/20 . 101/20)`.
To facilitate creation, it is also possible to create the same interval with
alternative notation:

    CL-USER> (ratmath:infsup 5 :abstol 5/100)             ;; 5, +/-.05
    (99/20 . 101/20)
    CL-USER> (ratmath:infsup 99/20 :abstol '(0 . 1/10))   ;; 99/20, -0/+.1
    (99/20 . 101/20)
    CL-USER> (ratmath:infsup 101/20 :abstol '(1/10 . 0))  ;; 101/20, -.1/+0
    (99/20 . 101/20)
    CL-USER> (ratmath:infsup 5 :tol 1/100)                ;; 5, +/-1%
    (99/20 . 101/20)
    CL-USER> (ratmath:infsup 5 :tol '(0 . 1/100))         ;; 5, -0%/+1%
    (5 . 101/20)

The gist is that `:tol` takes either an interval or an exact representing the
percent tolerance and `:abstol` uses absolute values +/- rather than percentages.
Refer to the documentation of the `infsup` function for further details.

## `with-interval-math` Blocks

From within a `ratmath:with-interval-math` block, some of the basic arithmetic
operations are replaced with interval aware variants. For instance:

    CL-USER> (ratmath:with-interval-math
               (* '(1 . 2) 5 (ratmath:infsup 3.3 :tol .01)))
    (16.335 . 33.329998)

Notice that the usual rules of floating point contagion apply. Since the
`infsup` was given arguments in floats, the result is a float. We can turn this
float back into rationals or exacts with:

    CL-USER> (ratmath:infsup '(16.335 . 33.329998) :limd 100)
    (49/3 . 3333/100)
    CL-USER> (ratmath:rat *)
    17

The `rat` function converts the interval `'(16.335 . 33.329998)` into the
_simplest_ number within. For this interval, it is 17. _Simplest_ may not be the
best term here, the full truth is its first number on the infinite Stern-Brocot
fraction tree that is recursively traversed in the process of analyzing the best
convergents and semi-convergents of a given continued fraction. What I mean to
illustrate here is that, under this definition, this number will rarely be the
midpoint of the interval, and also that mathematically correct rational
approximation is not as trivial as it may seem at first glance. There is some
really interesting algorithms and concepts (to math geeks, anyway) this
library is abstracting that many programs might gloss over. In fact, in the
beginning of 2020, the Linux kernel doesn't even have a fully correct
implementation which it uses (amongst other things) to calculate correct PLL
dividers for CPU clock rates. One that was close was published and posted, but
abandoned for non-obvious reasons probably having to do with Linux kernel
politics and style (or perhaps some microbenchmark suffered).

## Syntactic Sugar

Within a `with-interval-math` block, the full power of the Common Lisp macro
system is utilized to realize a cute feature regarding the parsing of numeric
literals. This can be illustrated most succinctly in the following single-line
piece of code:

    CL-USER> (ratmath:with-interval-math (* 2 ~5))
    (9 . 11)

The `with-interval-math` turns the numeric literal `~5` automatically into the
interval `'(4.5 . 5.5)` which is then multiplied by exactly 2 to return the
interval `'(9 . 11)`. The rules of conversion for ~ literals should not be
surprising. It should be noted that the interval will always result in rationals
even when normal numeric literal parsing rules would have it be a float. The
other key to remember regarding the tilde literal is they are parsed according
to the rules of significant figures. e.g. `~5` is `'(4.5 . 5.5)` but `~5.00` is
`'(4.995 . 5.005)` Exponential notation is honored as one might predict, `~1e3`
is `'(500 . 1500)`, always as rationals.

These numeric literals can also be parsed outside of a `with-interval-math`
block by passing a string to `parse-interval`. In `parse-interval` the tilde
character ornamentation is not necessary.

The tilde '~' character is also a function, but it behaves differently depending
on the context. Inside a `with-interval-math` block it turns an exact into an
interval and behaves the same way as the `infsup` function. Outside of this
block, it turns intervals into exacts according to some `&key` argument
controls. Refer to the documentation of the ~ function for full details, but
here are a few examples:

Random numbers for (e.g.) Monte Carlo analysis using a uniform probability
distribution within the interval:

    CL-USER> (ratmath:~ '(1 . 2) :random t)  ;; this will always be a float
    1.3231988

The `:discrete` boolean means to only return upper or lower limit. Assumes a
50/50 chance to return either, unless the `:alpha` option is supplied.


    CL-USER> (ratmath:~ '(1 . 2) :random t :discrete t) ;; random select upper/lower
    1
    CL-USER> (ratmath:~ '(1 . 2) :random t :discrete t :alpha 3/4) ;; 75% chance of upper
    2


Several types of calculations are only interested in worst-case/best-case which
will be either the upper or lower limit of the interval, e.g.:

    CL-USER> (ratmath:~ '(1/14 . 3/7) :upper t)
    3/7
    CL-USER> (ratmath:~ '(1/14 . 3/7) :lower t)
    1/14

## Other Tricks and Functions (useful in the REPL)

A common application of these algorithms are to print out a progression of
rational approximations of a given number as the size of the numerator and
denominator terms is allowed to increase. The following prints out the best
convergents and semi-convergents and their error in PPM or PPB
(parts-per-million/billion) on the way to system's pi constant:

    CL-USER> (ratmath:fractions pi :order 10)
    2'd3/1'd1 45070.341 PPM
    5'd22/3'd7 -402.499 PPM
    8'd179/6'd57 395.270 PPM
    9'd355/7'd113 -8.491D+1 PPB
    16'd52163/15'd16604 8.474D+1 PPB
    19'd312689/17'd99532 -9.277D-3 PPB
    20'd833719/19'd265381 2.774D-3 PPB
    21'd1146408/19'd364913 -5.128D-4 PPB
    23'd5419351/21'd1725033 -7.088D-6 PPB
    27'd80143857/25'd25510582 1.453D-7 PPB
    28'd245850922/27'd78256779 -1.410D-8 PPB
    30'd817696623/28'd260280919 1.531D-9 PPB
    32'd2698940791/30'd859099536 1.074D-10 PPB
    34'd9978066541/32'd3176117225 -9.265D-12 PPB
    35'd32633140414/34'd10387451211 3.833D-13 PPB
    38'd238410049439/37'd75888275702 -2.047D-14 PPB
    40'd747863288731/38'd238052278317 -2.855D-15 PPB
    41'd1257316528023/39'd400216280932 4.860D-16 PPB
    43'd5777129400823/41'd1838917402045 5.350D-17 PPB
    44'd10296942273623/42'd3277618523158 6.901D-19 PPB
    50'd884279719003555/49'd281474976710656 0.000D-1 PPB

The `:order 10` argument says to only print a best convergent/semi-convergent at
most once per decimal order of magnitude. This avoids flooding the output with
semi-convergents. If not specified, the default order is 2, which prints the
best approximation for every bit size width in the numerator and denominator.

The ##'d syntax at the beginning of each number is Verilog syntax to describe
the bit width of the constant. I wrote these routines originally to facilitate
writing Verilog in FPGAs for fractional clock dividers and PWM controllers. The
Verilog syntax for size is more convenient than manually counting digits to
figure how big of a register I have to instantiate.

It is worth noting that over half of the above convergents to pi will vary from
implementation to implementation. The pi constant is defined as a floating point
number in Common Lisp and the default behavior of ratmath is to convert floats
into rationals using the `rational` function rather than `rationalize`, which
takes into consideration the host machines limits of floating point precision.
(i.e. epsilon) If we instead prefer to stop the approximation at the end of the
floating point constant's precision, we can use:

    CL-USER> (ratmath:fractions (rationalize pi) :order 10)
    2'd3/1'd1 45070.341 PPM
    5'd22/3'd7 -402.499 PPM
    8'd179/6'd57 395.270 PPM
    9'd355/7'd113 -8.491D+1 PPB
    16'd52163/15'd16604 8.474D+1 PPB
    19'd312689/17'd99532 -9.277D-3 PPB
    20'd833719/19'd265381 2.774D-3 PPB
    21'd1146408/19'd364913 -5.127D-4 PPB
    23'd5419351/21'd1725033 -7.074D-6 PPB
    27'd80143857/25'd25510582 1.594D-7 PPB
    28'd245850922/27'd78256779 0.000D-1 PPB

## Pipe functions

A few public ratmath functions utilize a pattern unique to Common Lisp and
return whats described in chapter 25, "Streams and Delayed Evaluation", in the
book "Lisp, 3rd Edition" by Winston/Horn. The chapter describes a stream data
structure (that I have renamed to "pipe" to avoid name clash confusion), that
utilizes Lisp's lexical closures to create something akin to an infinite list. I
have modeled much of the internal implementation of this library around the
simple concepts described therein. Utilities to manipulate, map, filter, and
transform these data structures are included in pipe.lisp and are made public in
the ratmath package, though not specifically relating to the ratmath primary
interfaces. These routines are superficially documented in pipe.lisp, though
depending on familiarity with the above book or Lisp's lexical enclosures and
functional programming paradigms, might either seem extremely trivial or
extremely obtuse. This library was coded partly as an athletic
challenge/experiment in avoiding all usage of iteration/loops/assignments in
favor of recursion and functional programming. This (arbitrary) implementation
constraint was simultaneously pleasing and frustrating and the pipe construct
was an invaluable aid in realizing this.

The most likely useful pipe function is `ratmath:rat-pipe`, which takes as
argument an input number and optional exponent base number which defaults to 2.
This optional arg _n_ filters out semi-convergents from the same power-of-_n_
and only outputs the best approximation for each power-of-_n_ increase in
denominator/numerator.

    CL-USER> (ratmath:rat-pipe pi 10)
    (3 #<COMPILED-LEXICAL-CLOSURE (:INTERNAL RATMATH::PIPE-TRANSFORM) #x15B1D73E>)

Seeing the REPL output for this function shows that function returns a pipe. In
the above, the number 3 is the first element and the second element is actually
not an element at all, but a lexical closure that upon funcalling, will
calculate and expose another rational + lexical closure, ad infinitum.

Since we know that this pipe is not infinite and has an end, we can safely
convert the pipe into an ordinary list with `(ratmath:pipe-to-list *)` Note that
the real pi, as an irrational number, has an infinite continued fraction and
therefore an infinite pipe of rational approximations, but we are doing a
rational approximation on Common Lisp's floating point constant which has
finite precision and, therefore, a finite continued fraction.

    CL-USER> (ratmath:pipe-to-list *)
    (3 22/7 179/57 355/113 52163/16604 312689/99532 833719/265381 1146408/364913 
    5419351/1725033 80143857/25510582 245850922/78256779 817696623/260280919
    2698940791/859099536 9978066541/3176117225 32633140414/10387451211
    238410049439/75888275702 747863288731/238052278317 1257316528023/400216280932
    5777129400823/1838917402045 10296942273623/3277618523158
    884279719003555/281474976710656)

The `rat-pipe` does allow for irrational number approximation, you simply have
to create an infinite pipe of continued fraction terms to send as the first
argument instead of an atomic real number. An example generator is in
fractions.lisp in the function `ratmath:napiers-constant-generator` which
returns the infinite terms of the continued fraction expansion of Euler's number
_e_

    CL-USER> (ratmath:rat-pipe (ratmath:napiers-constant-generator))
    (3 #<COMPILED-LEXICAL-CLOSURE (:INTERNAL RATMATH::PIPE-TRANSFORM) #x15C8111E>)
    CL-USER> (ratmath::pipe-sink-until 
              (lambda (x) (> (integer-length (denominator x)) 4096)) 
              *)
    (41720850604724578859 .... ;; cut to not flood output with a 4096bit rational

Generating 8kbit integer rationals like this makes a good benchmark of Common
Lisp and how well it handles its bignums. Letting your rationals grow in size to
bignum territory likely will hurt performance significantly. Indeed, I would
predict large gains in speed sprinking declare forms throughout the
implementation of ratmath signifying intent to only ever use fixnums inputs and
outputs.

Another useful pipe function generates lists of ordered rational fractions
called Farey sequences. [Wikipedia](https://en.wikipedia.org/wiki/Farey_sequence). 
The function `ratmath:farey-pipe` is used
mostly for the implementation of `infsup`, but it is possible to use on its own,
e.g. to list out a farey sequence of order 7 (no fraction denominator greater
than 7):

    CL-USER> (ratmath:pipe-to-list (ratmath:farey-pipe 7))
    (1/7 1/6 1/5 1/4 2/7 1/3 2/5 3/7 1/2 4/7 3/5 2/3 5/7 3/4 4/5 5/6 6/7 1 7/6 
    6/5 5/4 4/3 7/5 3/2 5/3 7/4 2 7/3 5/2 3 7/2 4 5 6 7)

## Todo

* My attempt at allowing compile-time collapsing and constant folding of
  interval/ratmath needs further testing/review. Perhaps utilize numcl's
  constantfold package?
* Test routines.  Esp. for the interval ops.
* Maybe further distill and refine the public interfaces for working with
  Stern-Brocot fraction trees and Farey sequences.
* Incorporate any other useful algorithms people are thinking of when they hear
  of or google for a library named ratmath.
* More interval aware math functions in with-interval-math blocks
* To assist in calculating operations where the same interval appears more than
  once, create a function that loops on the block with the permutations of
  min/max on each interval and collects the hull of results. (This can avoid
  intervals unnecessarily widening)
* Maybe allow for gaussian or truncated gaussian probability distributions in
  the random conversion of intervals back to exacts.
