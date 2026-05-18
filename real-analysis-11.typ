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

= Problem 1: Weierstrass M-Test
Exercise 6.4.1

#theorem[
  For each $n in NN$, let $f_n$ be a function defined on a set $A subset.eq RR$, and let $M_n > 0$ be a real number satisfyin
  $
    abs(f_(n)(x)) <= M_n
  $
  for all $x in A$. If $sum_(n=1)^infinity M_n$ converges, then $sum_(n=1)^infinity f_n$ converges uniformly on $A$.
]
#proof[
  Let $epsilon > 0$ be given. By the Cauchy Criterion for Series applied to $sum_(n=1)^infinity M_n$, there exists some $N in NN$ such that whenever $n > m >= N$ we have
  $
    abs(M_(m+1) + M_(m+2) + ... + M_n) < epsilon .
  $

  Since every $M_i > 0$, this is equivalent to
  $
    M_(m+1) + M_(m+2) + ... + M_n < epsilon .
  $

  Then for any $x in A$ we have
  $
    abs(f_(m+1)(x) + f_(m+2)(x) + ... + f_(n)(x)) \
    <= & abs(f_(m+1)(x)) + abs(f_(m+2)(x)) + ... + abs(f_(n)(x)) \
    <= & M_(m+1) + M_(m+2) + ... + M_n \
    <  & epsilon .
  $

  By the Cauchy Criterion for Uniform Convergence of Series, since the choice of $N$ was independent of $x$, $sum_(n=1)^infinity f_(n)(x)$ converges uniformly on $A$.
]

= Problem 2: A trick for proving continuity at a point
Exercise 6.4.5

=== Proof idea

There is a cool idea happening in part (b). We can't apply the Weierstrass M-Test on all of $(-1,1)$ at once, because there's no single $M_n$ that will work for all $x$ in this interval: the defining series converges everywhere in this interval but its sum can be made unboundedly large by getting closer and closer to 1. Another way to put it is that there's no single convergent series of $M_n$ that dominates $abs(x^n/n)$ for _all_ $x in (-1,1)$. For any candidate $M_n$, there exist $x$ close enough to $1$ such that $abs(x^n slash n) > M_n$. If the $M_n$ get big enough to dominate, then their sum will diverge.

But the trick is that for any specific $x_0 in (-1,1)$ we can construct an interval that contains it, and produce an $M_n$ that bounds it there.

Note that we can't just use singleton sets ${x_0}$ and define $f$ on those to get around this problem, because continuity on singleton sets is trivial, or, to be more precise, doesn't extend to continuity on an open set containing the point. What we really want is to say that the function $f$ defined on $(-1,1)$ is continuous for any fixed $x_0 in (-1,1)$. If we tried to do this with singleton sets, we would have proved that $f: {x_0} -> RR$ is continuous at $x_0$. But this can't be extended to the statement that $f: (-1,1) -> RR$ is continuous at $x_0$. What's good about the idea that works is that we prove that $f: [-a,a] -> RR$ is continuous at $x_0 in [-a, a]$, from which we can say that $f: (-1,1) -> RR$ is continuous at $x_0 in (-1,1)$.

== Proofs

== (a)

#figure(
  image("real-analysis-11-2.png", width: 100%),
  caption: [Graphs of $h(x)$ with more and more terms],
)
#theorem[
  The function $h$ defined by the series
  $
    h(x) = sum_(n=1)^infinity x^n/n^2 = x + x^2/4 + x^3/9 + ...
  $
  is continuous on $[-1,1]$.
]
#proof[
  For $x in [-1,1]$,
  $
    abs(x^n) = abs(x)^n <= 1 .
  $

  Let $f_(n)(x) = x^n/n^2$. Then
  $
    abs(f_(n)(x)) <= 1/n^2 
  $
  when $x in [-1,1]$.

  Let $M_n = 1/n^2$. Then by the Cauchy Condensation Test (or, as proved several homeworks ago, since it is the series $sum_(n=1)^infinity 1 slash n^p$ with $p = 2 > 1$), the series $sum_(n=1)^infinity M_n$ converges. Therefore by the Weierstrass M-Test, the series $sum_(n=1)^infinity f_(n)(x)$ converges uniformly for $x in [-1,1]$. Therefore, since each $f_(n)$ is continuous (because polynomial), by the Term-by-term Continuity Theorem, $h(x)$ is continuous on $[-1,1]$.
]

== (b)

#figure(
  image("real-analysis-11-3.png", width: 100%),
  caption: [Graphs of $f(x)$ with more and more terms],
)

#theorem[
  Let
  $
    f(x) = sum_(n=1)^infinity x^n/n = x + x^2/2 + x^3/3 + ... .
  $
  Then for any fixed $x_0 in (-1,1)$, $f$ is continuous at $x_0$. Thus, $f$ is continuous on $(-1,1)$.
]
#proof[
  Since $x_0 in (-1,1)$, we have $abs(x_0) < 1$. So there exists some $a in (0,1)$ such that $abs(x_0) < a < 1$. (Note to myself: this isn't a consequence of the completeness of the reals. Just from being an ordered field. $QQ$ would have such an $a$ as well.)

  Let $M_n = a^n slash n$. Let $f_n$ be defined on the set $A = [-a,a]$ given by
  $
    f_(n)(x) = x^n/n .
  $
  For every $x in A$ we have
  $
    abs(x) <= a
  $
  so
  $
    abs(x^n) = abs(x)^n <= a^n
  $
  so
  $
    abs(x^n/n) <= a^n/n
  $
  so
  $
    abs(f_(n)(x)) <= M_n .
  $

  We compute
  $
    lim abs(M_(n+1)/M_n) 
     = & lim abs(frac(a^(n+1) slash (n+1), a^n slash n)) \
     = & lim abs(a) abs(n/(n+1)) \
     = & lim abs(a) abs(1/(1 + 1 slash n)) \
     = & abs(a) \
     < & 1
  $
  by the Algebraic Limit Theorem. So by the Ratio Test, the series $sum_(n=1)^infinity M_n$ converges.

  So by the Weierstrass M-Test, $sum_(n=1)^infinity f_(n)(x)$ converges uniformly for all $x in A$. Therefore, since each $f_(n)$ is continuous on $A$ since it is a polynomial, $f$ is continuous on $A$. So $f: [-a, a] -> RR$ is continuous at $x_0$.

  But then $f: (-1,1) -> RR$ is also continuous at $x_0$, since every sequence $(x_n) subset.eq (-1,1)$ that converges to $x_0$ is eventually entirely in $[-a, a] subset.eq (-1,1)$, so $(f(x_n)) -> f(x_0)$.

  So $f$ is continuous on $(-1,1)$.
]

= Problem 3: Uniform convergence of an alternating harmonic-like series
Exercise 6.4.6

=== Proof idea

I can see two ways of doing this but both involve a little bit of a "trick". One is to combine adjacent terms and apply the Weierstrass M-Test. The other is to use a fact we proved on the way to proving the Alternating Series Test via the Cauchy Criterion.

== Proofs

#figure(
  image("real-analysis-11-4.png", width: 100%),
  caption: [Graphs of $f(x)$ and the series obtained by differentiating term-by-term. Note the crazy behavior when $x < 0$],
)

Let
$
  f(x) = 1/x - 1/(x+1) + 1/(x+2) - 1/(x+3) + dots.h.c 
$
and
$
  f_(n)(x) = 1/(x+n-1) 
$
and
$
  g_(n)(x) = (-1)^(n+1) f_(n)(x) .
$

#lemma[
  $f$ is defined for all $x > 0$.
]
#proof[
  We use the Alternating Series Test. For all $x > 0$,
  $
    1/x > 1/(x+2) > dots.h.c > 1/(x+n) > 1/(x+n+1) > dots.h.c
  $
  and
  $
    1/(x+n) = (1 slash n)/(x slash n + 1) -> 0/1 = 0
  $
  by the Algebraic Limit Theorem.

  Therefore the series defining $f$ converges when $x > 0$ so $f$ is defined.
]

I will restate here (without proof) a fact I proved on the way to the Alternating Series Test. I did this with a bunch of casework involving the parity of $m-n$ and so forth, and you pointed out an inductive argument. The fact is:

#lemma[
  Let $(a_k)$ be a sequence satisfying

  (i) $a_1 >= a_2 >= dots.h.c >= a_k >= dots.h.c$, and

  (ii) $(a_k) -> 0$.

  Let $n > m >= 1$. Then
  $
    abs(a_(m+1) - a_(m+2) + a_(m+3) - dots.h.c plus.minus a_n) <= a_(m+1) .
  $

  Another way to state this is: let
  $
    s_n = a_1 - a_2 + a_3 - dots.h.c plus.minus a_n,
  $
  the sequence of partial sums of the alternating series
  $
    sum_(n=1)^infinity (-1)^(n+1) a_(n) .
  $

  Then
  $
    abs(s_n - s_m) <= a_(m+1) .
  $
]

#lemma[
  The series
  $
    sum_(n=1)^infinity g_(n)(x)
  $
  converges uniformly for $x > 0$.
]
#proof[
  Let $epsilon > 0$ be given. Pick any $N in NN$ such that
  $
    1/N < epsilon .
  $
  Such an $N$ exists because $(1/n) -> 0$ and by the Archimedean Property.

  Let $n > m >= N$. Then by the lemma above, for any $x > 0$ we have
  $
    & abs(g_(m+1)(x) + g_(m+2)(x) + ... + g_(n)(x)) \
    <= & abs(g_(m+1)(x)) \
    = & f_(m+1)(x) \
    = & 1/(x + m) \
    < & 1/m \
    <= & 1/N \
    < & epsilon .
  $
  The result follows by the Cauchy Criterion for Uniform Convergence of Series.
]

Since each term in the series is continuous, by uniform convergence we have continuity of the function $f$ on $(0,infinity)$.

Here's another proof of continuity using the Weierstrass M-Test and the trick from Problem 2:

#proof[
  Let $(s_n)$ be the sequence of partial sums of the original series. By the Alternating Series Test argument above, this sequence converges.
  
  By pairing adjacent terms we have
  $
    & 1/x - 1/(x+1) + 1/(x+2) - 1/(x+3) + dots.h.c \
    = & 1/(x(x+1)) + 1/((x+2)(x+3)) + dots.h.c .
  $
  Let
  $
    h_(n)(x) = 1/((x+2n-2)(x+2n - 1)) .
  $
  We claim that the original series equals
  $
    sum_(n=1)^infinity h_(n)(x) 
  $
  since the sequence of partial sums of this series is $(s_(2n))$, which is a subsequence of $(s_n)$, and subsequences of convergent sequences converge to the same limit.


  Let $x$ be given and pick some $a$ such that $0 < a < x$.
  Let
  $
    M_n = cases(
      1 slash a(a+1) & "if" n = 1,
      1 slash n^2 & "if" n > 1
    )
  $.

  Then for all $x > a$ and $n >= 1$ we have
  $
    h_(n)(x) <= M_n .
  $

  The series
  $
    sum_(n=1)^infinity M_n = 1/(a(a+1)) + sum_(n=2)^infinity 1/n^2
  $
  converges since it's a finite number plus the tail of a series known to converge.
  
  So the series converges uniformly on $(a,infinity)$ by the Weierstrass M-Test, so $f$ is continuous on $(a,infinity)$. By the same argument as in Problem 2, $f: (0, infinity) -> RR$ is continuous at $x$, so $f$ is continuous on $(0, infinity)$.
]

#lemma[
  $f$ is differentiable on $(0,infinity)$.
]
#proof[
  Let $x in (0, infinity)$ be given and pick some $a$ such that $0 < a < x$.

  Let
  $
    M_n = 1/(a + n - 1)^2 .
  $
  Then
  $
    sum_(n=1)^infinity M_n = 1/a^2 + sum_(n=2)^infinity M_n .
  $
  The second series above,
  $
    sum_(n=2)^infinity M_n = sum_(n=1)^infinity 1/(a + n)^2
  $
  converges by the comparison test against $sum_(n=1)^infinity 1 slash n^2$. Since $sum_(n=1)^infinity M_n$ is a finite term plus this convergent series, it converges.  
  
  Then the absolute value of the derivative of each term of the series for $f$ is
  $
    abs(g'_(n)(x)) = abs(-1/(x+n-1)^2)
  $
  so
  $
    abs(g'_(n)(x)) <= M_n
  $
  for all $x in [a, infinity)$. Therefore, by the Weierstrass M-Test, the series of derivatives of terms converges uniformly on $[a, infinity)$.

  Since $f$ converges on $(0,infinity)$ by the Term-by-Term Differentiability Theorem we have that $f: [a,infinity) -> RR$ is differentiable at $x$. By a similar argument as in Problem 2, since differentiability is a local property, we have that $f: (0, infinity) -> RR$ is differentiable at $x$, so it's differentiable on all of $(0, infinity)$.

  To make that "local property" bit rigorous: since $f: [a,infinity) -> RR$ is differentiable at $x$, the limit
  $
    lim_(y->x) frac(f(y) - f(x), y - x) = L
  $
  exists. Let $g(y)$ denote the difference quotient above as a function of $y$. Every sequence $(y_n) subset.eq (0, infinity)$ converging to $x$ is eventually in $[a, infinity)$ (by the definition of convergence and the triangle inequality). So $(g(y_n)) -> L$ when $g$ is considered as a function defined on $(0, infinity) backslash {x}$, therefore $f: (0, infinity) -> RR$ is differentiable at $x$.
]

= Problem 4: Continuity and differentiability of another series
Exercise 6.4.9

=== Proof idea

This is more practice with the Weierstrass M-Test. I found another place to use the AM-GM inequality, but we could have just done it in the usual way by taking derivatives and setting them to zero and looking at signs. Either way, proving uniform convergence of the derivative series gives us differentiability and _continuous_ differentiability in one fell swoop.

== Proofs

#figure(
  image("real-analysis-11-1.png", width: 100%),
  caption: [Graphs of $h(x)$ and the series obtained by differentiating term-by-term],
)

Let
$
  h(x) = sum_(n=1)^infinity 1/(x^2 + n^2)
$
and
$
  h_(n)(x) = 1/(x^2 + n^2) .
$

#theorem[
  $h$ is a continuous function defined on all of $RR$.
]
#proof[
  Let $M_n = 1 slash n^2$. Then
  $
    abs(h_(n)(x)) <= M_n
  $
  since $x^2 >= 0$. By the Weierstrass M-Test, the series $sum_(n=1)^infinity h_(n)(x)$ converges uniformly on all of $RR$. Since each $h_n$ is continuous on all of $RR$, so is $h$.
]

#theorem[
  $h$ is continuously differentiable on all of $RR$.
]
#proof[
  By the AM-GM inequality applied to $x^2$ and $n^2$, we have
  $
    (x^2 + n^2)/2 >= n abs(x)
  $
  so
  $
    (2 abs(x))/(x^2 + n^2) <= 1/n .
  $
  Also,
  $
    1/(x^2 + n^2) <= 1/n^2,
  $
  so
  $
    abs(h'_(n)(x)) = abs((-2x)/(x^2 + n^2)^2) <= 1/n^3 .
  $

  The series $sum_(n=1)^infinity 1 slash n^3$ converges since it's of the form $sum_(n=1)^infinity 1 slash n^s$ with $s = 3 > 1$. So by the Weierstrass M-Test, $sum_(n=1)^infinity h'_(n)(x)$ converges uniformly on all of $RR$. Since the original series converges, $h$ is differentiable on all of $RR$, and its derivative is given by the series
  $
    h'(x) = sum_(n=1)^infinity h'_(n)(x) .
  $

  Each term $h'_(n)(x)$ is continuous on all of $RR$ since it's a rational function whose denominator is always at least 1. Therefore, since the series for the derivative converges uniformly on all of $RR$, the derivative is continuous on all of $RR$.
]

= Problem 5: A monotone function continuous at every irrational point
Exercise 6.4.10

=== Proof idea

The main thing is to prove that each $u_n$ is continuous at every irrational point. For this I pulled out a little lemma that says, if a function is constant on some neighborhood $U$ of $c$ then the function is continuous at $c$. 

We still need uniform convergence of the $u_n$ at every $x in RR$. The Weierstrass M-Test and geometric series do the job once again.

== Proofs

#lemma[
  Let $f: A -> RR$ and $U subset.eq A$ be open. If $f$ is constant on $U$ then $f$ is continuous on $U$.
]
#proof[
  Let $epsilon > 0$ be given and let $c$ be any point in $U$. Since $U$ is open, there exists some $delta > 0$ such that the open ball $V_(delta)(c) subset.eq U$. Then whenever $abs(x-c) < delta$ we have $abs(f(x) - f(c)) = abs(f(c) - f(c)) = 0 < epsilon$ since $f$ is constant on $U$ therefore it's constant in $V_(delta)(c)$ as well. So $delta$ is a suitable reply to $epsilon$ in the definition of continuity.
]

Another way to state this is (based on a comment by Nic):

#theorem[
  A function $f: X -> Y$ is continuous iff for some open cover of $X$, $f$ is continuous on each open set in the cover.
]
#proof[
  ($=>$)

  Let $phi = {O_a: a in alpha}$ be an open cover of $X$ such that $f$ is continuous on every $O_a$. Let $x$ be any point in $X$. Then $x in O_b$ for some $O_b in phi$ since $phi$ is a cover of $X$. Let $V subset.eq Y$ be an open set containing $f(x)$. Since $f$ is continuous on $O_b$, there exists an open set $U subset.eq O_b$ containing $x$ such that $f(U) subset.eq V$. But then $U$ is an open subset of $X$ that contains $x$ and whose image is contained in $V$, proving that $f: X -> Y$ is continuous at $x$.

  ($arrow.l.double$)

  The open cover consisting of the whole space works: $phi = {X}$.

  Or, here's another argument:

  Let $f$ be continuous on $X$ and let $x in X$ be any point. Let $V_x subset.eq Y$ be any open set containing $f(x)$. By continuity, there exists some open $U_x subset.eq X$ such that $x in U_x$ and $f(U_x) subset.eq V_x$. Then
  $
    phi = {U_x : x in X}
  $
  is an open cover of $X$. We claim that $f$ is continuous on each $U_x$: let $y in U_x$ be any point, let $V_y$ be any open set containing $f(y)$. By continuity of $f$ on $X$, there exists some open $U_y subset.eq X$ such that $y in U_y$ and $f(U_y) subset.eq V_y$. Then $U_y inter U_x$ is an open subset of $U_x$ that contains $y$ and whose image is contained in $V_y$.
]

Let ${r_1, r_2, ...}$ be an enumeration of $QQ$. For each $r_n in QQ$, define
$
  u_(n)(x) = cases(
    1 slash 2^n quad & "for" x > r_n,
    0           quad & "for" x <= r_n .
  )
$

Now let $h(x) = sum_(n=1)^infinity u_(n)(x)$. 

#lemma[
  Every $u_(n)(x)$ is continuous at every irrational point.
]
#proof[
  Let $y in RR$ be irrational. Then either $y > r_n$ or $y < r_n$ and in both cases, $u_(n)$ is constant in an open ball of radius $abs(y-r_n) > 0$ centered at $y$. By the lemma above, $u_n$ is continuous at $y$.
]

#theorem[
  $h$ is defined on all of $RR$ and continuous at every irrational point.
]
#proof[
  Let $M_n = 1 slash 2^n$. Then $sum_(n=1)^infinity M_n$ is a convergent geometric series.

  Now, $u_(n)(x) <= M_n$ for every $n in NN$ and every $x in RR$ because it is either zero or equal to $M_n$. Therefore $sum_(n=1)^infinity u_(n)(x)$ converges uniformly for all of $RR$. So $h$ is defined on all of $RR$.

  Since each $u_n$ is continuous at every irrational point, each partial sum is also continuous at every irrational point by the Algebraic Continuity Theorem. Therefore by the Continuous Limit Theorem applied to the partial sums, $h$ is continuous at every irrational point.
]

#theorem[
  $h: RR -> RR$ is monotone.
]
#proof[
  Let $x >= y$. For every $r_n$ such that $y > r_n$, we have $x > r_n$ as well. So every nonzero term in the sum
  $
    sum_(n=1)^infinity u_(n)(y)
  $
  is nonzero in
  $
    sum_(n=1)^infinity u_(n)(x)
  $
  as well. Since every $u_(n)(x) >= 0$, we have $h(x) >= h(y)$.
]


Another way to show this (based on a comment by Nic):

#theorem[
  Let $f_n: A -> RR$ be a sequence of increasing functions defined on some set $A subset.eq RR$ such that the series $sum_(n=1)^infinity f_(n)(x)$ converges pointwise for all $x in A$. Then the function defined by the series is also increasing.
]
#proof[
  Let $(s_(n)(x))$ be the sequence of partial sums. Then each $s_n$ is the finite sum of increasing functions, so it's increasing.

  Since the series
  $
    s(x) = sum_(n=1)^infinity f_(n)(x)
  $
  converges pointwise, we have $(s_(n)(x)) -> s(x)$ for all $x in A$.

  Let $x_1, x_2 in A$ with $x_1 <= x_2$. Then
  $
    s_(n)(x_1) <= s_(n)(x_2)
  $
  for each $n in NN$, so by the Order Limit Theorem,
  $
    s(x_1) <= s(x_2),
  $
  i.e., $s$ is increasing.
]
