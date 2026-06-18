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

Theorems from the book that I'll use:

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

= Problem 1: Taylor coefficient formula
Exercise 6.6.3

#theorem[
  Let $f$ be an infinitely differentiable function defined on some interval $(-R,R)$ that has a power series expansion
  $
    f(x) = a_0 + a_1 x + a_2 x^2 + a_3 x^3 + dots.c .
  $
  Then
  $
    a_n = frac(f^((n))(0),n!) .
  $
]
#proof[
  By Theorem 6.5.7, the function $f$ is infinitely differentiable on $(-R,R)$ and by term-by-term differentiation we get that
  $  
    f^((n))(x) = sum_(k=n)^infinity k (k-1) dots (k-n+1) a_k x^(k-n) .
  $

  Evaluating this at $x=0$, all terms but the first are zero, so we get
  $
    f^((n))(0) = n (n-1) (n-2) dots 3 dot 2 dot 1 dot a_n
  $
  and since $n! != 0$ we may divide to obtain
  $
    a_n = frac(f^((n))(0), n!)
  $
  as desired.
]
= Problem 2: Taylor series for $e^x$
Exercise 6.6.5

== (a)

Using the formula proved in Problem 1, if $f(x) = e^x$ has a power series expansion then
$
  a_n = e^0/n! = 1/n!
$
where we use the the fact that $e^x$ is its own derivative, which Abbott says is fair game for this section.

Now we show uniform convergence on an arbitrary interval $(-R,R)$:

Let $S_(N)(x)$ be the $N$th partial sum of this series. Then, using Lagrange's Remainder Theorem, the error $E_(N)(x) = e^x - S_(N)(x)$ is
$
  E_(N)(x) = frac(f^((N+1))(c), (N+1)!) x^(N+1) = frac(e^c,(N+1)!) x^(N+1)
$

for some $abs(c) < abs(x) < abs(R)$.

Taking absolute values on both sides and using that fact that the exponential function is monotonic, and that $abs(x) < R$ this is bounded by
$
  abs(E_(N)(x)) <= frac(e^R R^(N+1), (N+1)!) .
$

Now we use the Ratio Test for Sequences: the ratio of successive terms of this sequence is
$
  R/(N+2)
$
which converges to 0. So the sequence itself converges to 0, so $abs(E_(N)(x)) -> 0$ independent of $x$, so the series converges uniformly to $e^x$ on $(-R,R)$.

== (b)

We have shown that
$
  e^x = f(x) = sum_(n=0)^infinity x^n/n!
$
with uniform convergence on any interval $(-R,R)$.

Using Theorem 6.5.7 we may differentiate term-by-term to obtain
$
  f'(x) = sum_(n=1)^infinity frac(n x^(n-1),n!) = sum_(n=1)^infinity x^(n-1)/(n-1)!
$
which is the same as the original series, just with a re-indexing. Thus
$
  f'(x) = f(x) = e^x .
$

== (c)

Substituting $-x$ for $x$ in the series above, we obtain
$
  e^(-x) = 1 - x + x^2/2! - x^3/3! + x^4/4! - dots.c .
$

Formally manipulating the series product $e^x e^(-x)$ we get
$
  e^x e^(-x) = 1 + x (1 - 1) + x^2 (1/2! - 1 + 1/2!) + x^3 (-1/3! + 1/3! - 1/2! + 1/2!) + ... dots.c
$
for the first few terms. By collecting terms for each coefficient $x^n$ we get
$
  sum_(k=0)^n frac((-1)^(n-k), k! (n-k)!) = 1/n! sum_(k=0)^n binom(n,k) (-1)^(n-k)
$
which is the binomial expansion of $(1-1)^n = 0$. So every coefficient evaluates to zero except for the leading term 1. In other words, $e^x e^(-x) = 1$.

= Problem 3: Some examples of Taylor series with certain properties
Exercise 6.6.7

== (a)

Let
$
  g(x) = 1/(1+x^2) .
$

It is infinitely differentiable on all of $RR$ since $x^2 + 1 != 0$ for any $x in RR$. This is the sum of the geometric series
$
  1 - x^2 + x^4 - x^6 + dots.c ,
$
but since power series representations are unique, this is also its Taylor series.

This is a geometric series with common ratio $-x^2$ and therefore converges only for $abs(x^2) < 1$, i.e., for $x in (-1,1)$, and diverges outside this interval.

This function is perfectly smooth at $x = plus.minus 1$; there's a singularity but it's in the complex plane.

== (b)

Let
$
  g(x) = cases(
    exp(-1/x^2) & "for" x != 0,
    0           & "for" x = 0 
  )
$
and
$
  h(x) = sin(x) + g(x) .
$

As stated in the book, $g(x)$ is infinitely differentiable and all its Taylor coefficients are zero. By linearity of differentiation, the coefficients of the Taylor series for $h(x)$ are the sum of the respective coefficients of $sin(x)$ and $g(x)$. So the Taylor series for $h(x)$ is the same as the Taylor series for $sin(x)$ (and therefore converges to $sin(x)$) but $h(x) != sin(x)$ for all $x != 0$ since $g(x) != 0$ for $x != 0$.

== (c)

Let
$
  f(x) = cases(
    exp(-1/x^2) & "for" x > 0,
    0           & "for" x <= 0 .
  )
$

At $x=0$ all the derivatives of this function are zero: the right hand limits are zero by the result of Exercise 6.6.6, and the left hand limits are zero since the function is just constant there. Hence, all Taylor coefficients of this function are zero.

So the Taylor series for this function converges to 0 everywhere, i.e., it converges to $f(x)$ if and only if $x <= 0$.

= Problem 4: A weaker form of Lagrange's Remainder Theorem
Exercise 6.6.8

== (a)

#lemma[
  If $g$ and $h$ are differentiable on $[0,x]$ with $g(0) = h(0)$ and $g'(t) <= h'(t)$ for all $t in [0,x]$, then $g(t) <= h(t)$ for all $t in [0,x]$.
]
#proof[
  The function
  $
    f(t) = h(t) - g(t)
  $
  satisfies the hypotheses for the Mean Value Theorem on the interval $[0,t]$ for any $t in (0,x]$, so we have
  $
    frac(f(t) - f(0), t - 0) = f'(c)
  $
  for some $c in (0,t)$. But $f(0) = 0$ since $g(0) = h(0)$ and $f'(c) >= 0$ since $f'(t) = h'(t) - g'(t) >= 0$. And $t > 0$ so multplication preserves the inequality. So
  $
    f(t) = h(t) - g(t) >= 0
  $
  when $t in (0,x]$. For $t = 0$ the statement holds as well since $g(0) = h(0)$.
]

== (b)

#theorem[
  Let $f$, $S_N$ and $E_N$ be as Theorem 6.6.3 and take $0 < x < R$. If
  $
    abs(f^((N+1))(t)) <= M
  $
  for all $t in [0,x]$ then
  $
    abs(E_(N)(x)) <= frac(M x^(N+1),(N+1)!) .
  $
]
#proof[
  The Taylor coefficients are chosen so that the function $f$ and the polynomial $S_N$ have the same derivatives at zero, at least up through the $N$th derivative, after which $S_N$ becomes the zero function. In other words,
  $
    f^((n))(0) = S^((n))_(N)(0)
  $
  for all $0 <= n <= N$, which implies the error function
  $
    E_(N)(x) = f(x) - S_(N)(x)
  $
  satsifies
  $
    E^((n))_(N)(0) = 0 "for all" n = 0,1,2,...,N .
  $

  Take
  $
    g(t) = E^((N))_(N)(t)
  $
  and
  $
    h(t) = M t
  $
  Then $g(0) = h(0) = 0$, and $g'(t) = f^((N+1))(t)$ since the $N+1$th derivative of $S_N$ is zero. So we may apply the lemma above to both sides of
  $
    -M <= f^((N+1))(t) <= M
  $
  to obtain
  $
    -M t <= E^((N))_(N)(t) <= M t .
  $

  The antiderivatives of these functions are $frac(M t^2,2)$ and $E^((N-1))_(N)(t)$ which again satisfy the conditions of the lemma. So we get
  $
    frac(-M t^2,2) <= E^((N-1))_(N)(t) <= frac(M t^2,2)
  $
  and, repeating this $N$ times in total,
  $
    frac(-M t^(N+1), (N+1)!) <= E_(N)(t) <= frac(M t^(N+1), (N+1)!) .
  $
  This holds for all $t in [0,x]$, so in particular it holds for $t=x$, giving the desired result.
]

= Problem 5
Exercise 6.6.9
= Problem 6
Exercise 6.6.10
