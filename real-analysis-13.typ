#set page(numbering: "1")
#import "@preview/ctheorems:1.1.3": *
#import "@preview/physica:0.9.7": evaluated

#show: thmrules
#let lemma = thmbox("lemma", "Lemma", base: none)
#let theorem = thmbox("theorem", "Theorem", base: none)
#let definition = thmbox("definition", "Definition", base: none)
#let problem = thmbox("problem", "Problem", base: none)
#let proof = thmproof("proof", "Proof")
#let remark = thmbox("remark", "Remark")
#set math.mat(delim: "[")
#set math.equation(numbering: "(1)")

#show math.equation: it => {
  if it.block and not it.has("label") and it.numbering != none {
    counter(math.equation).update(v => v - 1)
    
    // Fix: Create a dictionary of fields, remove 'body', 
    // and pass 'it.body' positionally.
    let fields = it.fields()
    let _ = fields.remove("body") 
    
    math.equation(it.body, ..fields, numbering: none)
  } else {
    it
  }
}

#show heading.where(level: 1): it => {
  pagebreak(weak: true)
  it
}

#outline(depth: 1)

Exercises are from Stephen Abbott's _Understanding Analysis_, Second Edition.

I'll state some theorems here from the book that don't have names:

#theorem[6.5.1 If a power series $sum_(n=1)^infinity a_n x^n$ converges at some point $x_0 in RR$, then it converges absolutely for any $x$ satisfying $abs(x) < abs(x_0)$.]

#theorem[6.5.5 If a power series converges pointwise on the set $A subset.eq RR$, then it converges uniformly on any compact set $K subset.eq A$. As a consequence, it is continuous at every point at which it converges.]

#theorem[6.5.6 If $sum_(n=0)^infinity a_n x^n$ converges for all $x in (-R,R)$, then the differentiated series $sum_(n=1)^infinity n a_n x^(n-1)$ converges at each $x in (-R,R)$ as well. Consequently, the convergence is uniform on compact sets contained in $(-R,R)$.]

#theorem[6.5.7 Assume
$
  f(x) = sum_(n=0)^infinity a_n x^n
$
converges on an interval $A subset.eq RR$. The function $f$ is continuous on $A$ and differentiable on any open interval $(-R,R) subset.eq A$. The derivative is given by
$
  f'(x) = sum_(n=1)^infinity n a_n x^(n-1) .
$
Moreover, $f$ is infinitely differentiable on $(-R,R)$, and the successive derivatives can be obtained via term-by-term differentiation of the appropriate series.
]

= Problem 1: An alternating power series
Exercise 6.5.1

Define the function $g$ by the power series
$
  g(x) = x - x^2/2 + x^3/3 - x^4/4 + dots.c .
$

Let
$
  a_n = (-1)^(n+1) x^n/n .
$
== (a)

Let $x in (-1,1)$. Then $abs(x) < 1$ and
$
  lim_(n->infinity) abs(a_(n+1)/a_n) = lim_(n->infinity) abs(x) abs(n/(n+1)) = abs(x) < 1,
$
so by the Ratio Test the series converges pointwise when $abs(x) < 1$. By Theorem 6.5.5 it converges uniformly on compact subsets of $(-1,1)$ and is continuous on $(-1,1)$.

At $x=1$ the series converges by the Alternating Series Test, since
$
  1 > 1/2 > dots.c > 1/n > dots.c 
$
and $(1/n) -> 0$. So the power series defining $g$ is defined on $(-1, 1]$. By Theorem 6.5.5 it converges uniformly on every compact subset of $(-1, 1]$ and it's continuous on $(-1,1]$. 

At $x=-1$ this is (the negative of) the harmonic series, so it diverges (by the Cauchy Condensation Test). So $g$ is not continuous on $[-1,1]$.

The series cannot converge for any point $x$ with $abs(x) > 1$ because that would imply convergence for all $y$ with $abs(y) < abs(x)$, including $y = -1$, contradicting divergence of the harmonic series.

== (b)

Since the series defining $g(x)$ converges on $(-1,1)$, by Theorem 6.5.6 $g'(x)$ is certainly defined for $x in (-1,1)$ and given by

$
  g'(x) = 1 - x + x^2 - x^3 + dots.c \
  = 1/(1+x)
$

on this interval.

At $x=-1$ the function is not defined, so the derivative is also not defined.

At $x=1$ the differentiated series diverges. But the derivative still exists: using the definition of derivative,
$
  g'(1) = lim_(h -> 0^-) frac(g(1+h) - g(1), h) .
$

The function $g$ is continuous on $[1+h, 1]$ and differentiable on $(1+h,1)$, so the Mean Value Theorem applies to the difference quotient:

$
  frac(g(1+h) - g(1), h) = 1/(1+c_h)
$
for some $c_h in (1+h,1)$, so
$
  g'(1) = lim_(h -> 0^-) 1/(1+c_h)
$
for some $c_h in (1+h,1)$. By the Squeeze Theorem, $c_h->1$ as $h->0^-$. By the Algebraic Limit Theorem, $1/(1+c_h) -> 1/2$ as $c_h->1$. So the limit exists and $g'(1) = 1/2$. Since this is the value of $1/(1+x)$ at $x=1$, we can summarize the result by saying that
$
  g'(x) = 1/(1+x)
$
for $x in (-1,1]$.

= Problem 2: Power series with various properties
Exercise 6.5.2

== (a) Converges for every value of $x in RR$

The power series with $a_n = 0$ for all $n$ converges for all $x in RR$.

A less trivial example is
$
  a_n = 1/n!
$

which is converges absolutely for all $x in RR$ by the Ratio Test because

$
  lim_(n -> infinity) abs(frac(a_(n+1) x^(n+1), a_n x^n)) = lim_(n->infinity) abs(x)/(n+1) = abs(x) lim_(n->infinity) 1/(n+1) = 0 .
$


== (b) Diverges for every value of $x in RR$

The request is impossible because every power series converges to $a_0$ at $x = 0$.

The power series with

$
  a_n = n!
$

diverges for all $x in RR \\ {0}$ by the Ratio Test because

$
  lim_(n->infinity) abs(frac(a_(n+1) x^(n+1), a_n x^n)) = abs(x) lim_(n->infinity) n -> infinity .
$

== (c) Converges absolutely for all $x in [-1, 1]$ and diverges off of this set

The power series with

$
  a_n = 1/n^2
$

converges absolutely at $x = plus.minus 1$ because at those points, the sum of the absolute values of the terms is $sum_(n=1)^infinity 1 slash n^2$, the Euler series.

By Theorem 6.5.1, it converges absolutely for all $x$ satisfying $abs(x) < 1$, so it converges absolutely on $(-1,1)$. Together with the endpoints, we have absolute convergence on $[-1,1]$.

Outside that closed interval, it diverges by the Ratio Test:

$
  lim_(n->infinity) abs(frac(a_(n+1) x^(n+1), a_n x^n)) = abs(x) lim_(n->infinity) frac(n^2, (n+1)^2) = abs(x) > 1 .
$

== (d) Converges conditionally at $x=-1$ and converges absolutely at $x=1$

The request is impossible: conditional convergence of $sum_(n=0)^infinity a_n x^n$ at $x = -1$ requires that $sum_(n=0)^infinity abs(a_n)$ diverges, which contradicts absolute convergence at $x=1$.

== (e) Converges conditionally at both $x=-1$ and $x=1$

Idea: use the Alternating Harmonic Series, and substitute $x^2$ for $x$ to get the same behavior at both endpoints.

Consider the series

$
  1 - x^2/2 + x^4/3 - x^6/4 + x^8/5 - dots.c .
$

At $x = plus.minus 1$ this is the Alternating Harmonic Series which converges by the Alternating Series Test. The convergence is conditional because when we take absolute values we get the Harmonic Series, which diverges.

The precise formula for the coefficients is

$
  a_n = cases(
    0 & "if" n "is odd",
    1 slash (1 + n/2) & "if" n eq.triple 0 mod 4,
    -1 slash (1 + n/2) & "if" n eq.triple 2 mod 4 .
  )
$


= Problem 3: Absolute convergence at $c$ $=>$ uniform convergence on $[-abs(c), abs(c)]$
Exercise 6.5.3

#theorem[
  If a power series $sum_(n=0)^infinity a_n x^n$ converges absolutely at a point $x_0$, then it converges uniformly on the closed interval $[-c, c]$, where $c = abs(x_0)$.
]
#proof[
  Define
  $
    M_n = abs(a_n x_0^n)
  $

  and let $x$ be any point in $[-c, c]$ where $c = abs(x_0)$. Then
  $
    abs(x) <= abs(x_0)
  $
  so, by the multiplicative property of the absolute value function,
  $
    abs(a_n x^n) <= abs(a_n x_0^n) = M_n .
  $

  Absolute convergence of $sum_(n=0)^infinity a_n x_0^n$ is equivalent to saying that the sum $sum_(n=0)^infinity M_n$ converges. By the Weierstrass M-Test, $sum_(n=0)^infinity a_n x^n$ converges uniformly whenever $x in [-c,c]$.
]

= Problem 4: Power series can be differentiated term-by-term on open intervals
Exercise 6.5.5

== (a) If $0 < s < 1$ then $n s^(n-1)$ is bounded

This is kind of a roundabout and overkill way but it uses the tools we've already developed and is very easy.

#proof[
Define

$
  a_n = n s^(n-1) .
$

Then

$
  lim_(n->infinity) abs(frac(a_(n+1), a_n)) = abs(s) lim_(n->infinity) frac(n+1,n) = abs(s) < 1
$

so by the Ratio Test, the series

$
  sum_(n=0)^infinity a_n
$

converges. Therefore the terms $(a_n) -> 0$, and convergent sequences are bounded.
]

Of course it's a bit of a smell that we're involving a series convergence test when there's no series here, really. We could probably extract the relevant bits from the proof of the Ratio Test for series. The sketch is:

#proof[
Since $lim_(n->infinity) abs(frac(a_(n+1), a_n)) -> s < 1$, pick some $s < r < 1$.

By the definition of sequence convergence, there exists some $N in NN$ such that for all $n >= N$ we have 

$
  a_n < r a_(n-1)
$

so

$
  a_(N+k) < r^k a_N .
$

The RHS converges to zero because $(r^k) -> 0$, and the LHS is positive, so by the Squeeze Theorem it converges to 0.
]

== (b) The rest of the proof

#lemma[
  If $sum_(n=0)^infinity a_n x^n$ converges, then so does $sum_(n=1)^infinity a_n x^(n-1)$.
]
#proof[
  If $x=0$ then all terms of the second sum after $n=1$ are zero, so it converges to $a_1$. Otherwise, let $s_n$ be the $n$'th partial sum of the series
  $
    sum_(n=0)^infinity a_n x^n 
  $
  and $t_n$ the $n$'th partial sum of the series
  $
    sum_(n=1)^infinity a_n x^(n-1) .
  $
  Then
  $
    t_n = (s_n-a_0)/x
  $
  so by the Algebraic Limit Theorem, the sequence $(t_n)$ converges.
]

#lemma[
  If $sum_(n=0)^infinity a_n x^n$ converges for $x in (-R,R)$ then it converges absolutely for all $x in (-R,R)$.
]
#proof[
  Let $x in (-R,R)$ and pick $abs(x) < x_0 < R$. By the hypothesis, the series converges at $x_0$. By Theorem 6.5.1, the series converges absolutely at $x$. Since $x$ was arbitrary, the series converges absolutely for all points in the open interval.
]

#theorem[
  If $sum_(n=0)^infinity a_n x^n$ converges for all $x in (-R,R)$, then the differentiated series $sum_(n=1)^infinity n a_n x^(n-1)$ converges at each $x in (-R,R)$ as well. Consequently, the convergence is uniform on compact sets contained in $(-R,R)$.
]
#proof[
  Let $x in (-R,R)$. If $x=0$ then the differentiated series converges since all terms after the first (constant) term are zero and the theorem is true.

  Otherwise, pick some $t$ satisfying $abs(x) < t < R$. Write
  $
    n a_n x^(n-1) = n a_n (x^(n-1)/t^(n-1)) t^(n-1) = n (x/t)^(n-1) a_n t^(n-1) .
  $

  Taking absolute values, we have
  $
    abs(n a_n x^(n-1)) = n abs(x/t)^(n-1) abs(a_n t^(n-1)) .
  $

  By the choice of $t$ we have $0 < abs(x/t) < 1$ so, by part (a), the factor
  $
    n abs(x/t)^(n-1)
  $
  is bounded. Let $M > 0$ be a bound. Then we may divide by $M$ to obtain
  $
    abs(n a_n x^(n-1))/M <= abs(a_n t^(n-1)) .
  $

  Applying Lemma 1 and then Lemma 2, the series
  $
    sum_(n=1)^infinity a_n t^(n-1)
  $
  converges absolutely. So by the comparison test,
  $
    sum_(n=1)^infinity frac(n a_n x^(n-1),M)
  $
  converges absolutely. By the Algebraic Limit Theorem, since $M$ is just a constant, the desired series
  $
    sum_(n=1)^infinity n a_n x^(n-1)
  $
  converges absolutely, and therefore converges. Since the choice of $x$ was arbitrary, convergence holds for all $x in (-R,R)$. By Theorem 6.5.5, it converges uniformly on every compact subset of $(-R,R)$.
]

= Problem 5: Radius of convergence is $1/L$ where $L = lim_(n->infinity) abs(a_(n+1) slash a_n)$
Exercise 6.5.7

Let $sum a_n x^n$ be a power series with $a_n != 0$, and assume
$
  L = lim_(n->infinity) abs(a_(n+1)/a_n)
$
exists.

== (a) Finite radius of convergence

#theorem[
  If $L != 0$, then the series converges for all $x in (-1 slash L, 1 slash L)$.
]
#proof[
  Suppose that $x in (-1 slash L, 1 slash L)$. If $x = 0$ then the power series converges to $a_0$ because all other terms are 0.

  Otherwise, since $a_n != 0$ and $x != 0$, the terms $a_n x^n != 0$ and we may apply the Ratio Test:
  $
    lim_(n->infinity) abs(frac(a_(n+1)x^(n+1), a_n x^n)) = abs(x) lim_(n->infinity) abs(a_(n+1)/a_n) = abs(x) L < 1
  $
  since $abs(x) < 1 slash L$. By the Ratio Test, the series converges. Since $x$ was arbitrary, the series converges for all $x in (-1 slash L, 1 slash L)$.
]

== (b) Infinite radius of convergence

#theorem[
  If $L = 0$, then the series converges for all $x in RR$.
]
#proof[
  Let $x$ be any real number. If $x = 0$ then the power series converges to $a_0$ because all other terms are 0.

  Otherwise, since $a_n != 0$ and $x != 0$, the terms $a_n x^n != 0$ and we may apply the Ratio Test:
  $
    lim_(n->infinity) abs(frac(a_(n+1)x^(n+1), a_n x^n)) = abs(x) lim_(n->infinity) abs(a_(n+1)/a_n) = abs(x) L = 0 < 1
  $
  since $L = 0$ and $abs(x)$ is a finite number. By the Ratio Test, the series converges. Since $x$ was arbitrary, the series converges for all $x in RR$.
]

== (c) $lim sup$ version

First let's prove the Ratio Test with the $lim sup$ hypothesis. I'll follow the same steps as Abbott's Exercise 2.7.9 that we did in problem set number 2:

#theorem[
  Given a series $sum_(n=1)^infinity a_n$ with $a_n != 0$, suppose that
  $
    L = lim_(n->infinity) sup {abs(a_(k+1)/a_k): k >= n}
  $
  exists and
  $
    L < 1 .
  $
  Then the series converges absolutely.
]
#proof[
  Pick some $r$ satisfying $L < r < 1$ and let $epsilon = r - L > 0$ in the definition of sequence convergence to get that there exists an $N in NN$ such that for any $n >= N$,
  $
    abs( sup{abs(a_(k+1)/a_k): k >= n}  - L) < epsilon
  $
  so
  $
    -epsilon < sup{abs(a_(k+1)/a_k): k >= n}  - L < epsilon = r - L .
  $

  Adding $L$ to both sides of the second of these two inequalities, we find that
  $
    sup{abs(a_(k+1)/a_k): k >= n} < r .
  $

  The supremum is an upper bound, so
  $
    abs(a_(n+1)/a_n) <= sup{abs(a_(k+1)/a_k): k >= n} < r
  $
  so
  $
    abs(a_(n+1)) < abs(a_n) r
  $ <eq1>
  for all $n >= N$.

  (The rest of this proof goes the same as before.)

  Now $L >= 0$ by the Order Limit Theorem since it is the limit of a sequence of suprema of sets of non-negative numbers (absolute values). So $0 < r < 1$, so $abs(r) < 1$ and the geometric series
  $
    sum_(n=1)^infinity r^n
  $
  converges. Since $abs(a_N)$ is just a fixed number,
  $
    abs(a_N) sum_(n=1)^infinity r^n
  $
  converges.

  For any $m >= 1$, by applying @eq1 $m$ times we get
  $
    abs(a_(N+m)) < abs(a_N) r^m .
  $ <eq2>

  We split the infinite sum into a finite prefix of the first $N$ terms and the infinite tail:
  $
    & sum_(n=1)^infinity abs(a_n) \
    = & sum_(n=1)^N abs(a_n) + sum_(n=N+1)^infinity abs(a_n) \
    = & sum_(n=1)^N abs(a_n) + sum_(m=1)^infinity abs(a_(N+m))
  $
  which is a finite sum plus an infinite series. That series converges by the Comparison Test: @eq2 shows that each term is less than the corresponding term of the series $abs(a_N)sum r^n$ which we proved converges.

  Since the series converges absolutely, it converges.
]

Before proceeding we'll need this

#lemma[
  Let $A subset.eq RR$ be a bounded non-empty set and $C >= 0$ any constant. Then
  $
    sup {C x : x in A} = C sup A .
  $
]
#proof[
  Let $s = sup A$ and $B = {C x : x in A}$. If $C = 0$ then $C s = 0$ and $B = {0}$, whose supremum is zero.

  Otherwise, $C > 0$. Since $s$ is an upper bound, we have
  $
    s >= x
  $
  for all $x in A$, so
  $
    C s >= C x
  $
  for all $x in A$, so
  $
    C s >= y
  $
  for all $y in B$. In other words, $C s$ is an upper bound for $B$.

  Let $epsilon > 0$ be given. Then because $s$ is the _least_ upper bound of $A$, there exists some element $m in A$ such that
  $
    m > s - epsilon/C 
  $
  so
  $
    C m > C s - epsilon .
  $

  Since $C m$ is a member of $B$ whenever $m in A$ and $epsilon$ is arbitrary, the inequality above shows that $C s - epsilon$ is never an upper bound for $B$. Thus, $C s$ is the _least_ upper bound of $B$.
]

We apply this more general Ratio Test to the power series $sum_(n=0)^infinity a_n x^n$. When $x = 0$ then the power series always converges, so in the following we assume $x != 0$. Also, we are given that $a_n != 0$, so we may compute
$
  lim_(n->infinity) sup {abs(frac(a_(k+1) x^(k+1),a_k x^k)) : k >= n} = abs(x) L
$
by the multiplicative property of the absolute value function, the lemma above applied with $C = abs(x)$, and the Algebraic Limit Theorem.

The rest of the argument goes as before: if $L != 0$ and $x in (-1 slash L, 1 slash L)$ then $abs(x) < 1 slash L$ so $abs(x) L < 1$ so by the stronger form of the Ratio Test just proved, the series converges. And if $L = 0$ then $abs(x) L = 0 < 1$ so the series converges. 

= Problem 6: Power series are unique; and the exponential function
Exercise 6.5.8

== (a)
#theorem[
  If
  $
    sum_(n=0)^infinity a_n x^n = sum_(n=0)^infinity b_n x^n
  $
  for all $x$ in an interval $(-R,R)$, then $a_n = b_n$ for all $n=0,1,2 dots$.
]
#proof[
  Since $0 in (-R,R)$, the two series converge to the same value at $x = 0$. Thus $a_0 = b_0$.

  Let $f(x) = sum_(n=0)^infinity a_n x^n = sum_(n=0)^infinity b_n x^n$ be the function that both series converge to. By Theorem 6.5.7, $f$ is infinitely differentiable on $(-R,R)$ and the $k$'th derivative of $f$ has two series representations, given by term-by-term differentiation of the two series representations of $f$:
  $
    f^((k))(x) = & sum_(n=k)^infinity n (n-1) dots (n-k+1) a_n x^(n-k) \
             = & sum_(n=k)^infinity n (n-1) dots (n-k+1) b_n x^(n-k) 
  $
  where $k >= 1$.
  
  Since $0 in (-R,R)$, $f$ is infinitely differentiable at $x=0$. Since both series represent the same function $f^((k))$ they must agree at $x=0$.

  When $x=0$ all terms except the first term, $n=k$, are zero. So we get
  $
    k! a_k = k! b_k
  $
  so, since $k! != 0$ for any $k >= 1$, we have
  $
    a_k = b_k
  $
  for all $k >= 1$.
]

== (b)

Let
$
  f(x) = sum_(n=0)^infinity a_n x^n = a_0 + a_1 x + a_2 x^2 + a_3 x^3 + dots.c
$
converge on $(-R,R)$, and $f'(x) = f(x)$ for all $x in (-R,R)$ and $f(0) = 1$.

Then $a_0 = 1$ by evaluating the series at $x=0$.

By Theorem 6.5.7,
$
  f'(x) = sum_(n=1)^infinity n a_n x^(n-1) = 1 a_1 + 2 a_2 x + 3 a_3 x^2 + dots.c
$
for all $x in (-R,R)$. Since $f(x) = f'(x)$ is given, the two power series represent the same function on $(-R,R)$ so by the part (a) the corresponding coefficients of $x^n$ must be equal. So
$
  a_(n+1) = a_n / (n+1) 
$
for $n >= 0$. By applying this recurrence $n$ times to $a_0 = 1$ we get
$
  a_n = 1/n! .
$

