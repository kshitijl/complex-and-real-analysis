#set page(numbering: "1")
#import "@preview/ctheorems:1.1.3": *
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

= Problem 1: Functional limits and function composition
(Exercise 4.3.4)

=== Proof Idea

This question is all about the difference between continuity and functional limits, namely, what's going on exactly _at_ $c$. For functional limits, anything could be happening there. But for continuous functions, $lim_(x->c) f(x)$ must actually equal $f(c)$.

We're looking for a counterexample to a statement we _know_ is true for continuous functions,. So we've got to mess around with the value at $c$ and make it different from the limit.

== (a)

Let
$
  g(x) = cases(
    0 & "if" x = 0,
    1 & "otherwise"
  ) \
  "and"\
  f(x) = 0 .
$

Then $lim_(x->0) f(x) = 0$ and $lim_(x->0) g(x) = 1$, but $lim_(x->0) g(f(x)) = 0$ since $g(f(x)) = 0$ for all values of $x$.

== (b)

Suppose $f$ and $g$ are continuous. Since the functions are defined on all of $RR$, every point $c in RR$ is a limit point of the domain. Therefore
$
  lim_(x->p) f(x) = f(p) = q\
  "and" \
  lim_(x->q) g(x) = g(q) = r.
$

Also, $g compose f$ is continuous, as proved in the textbook and also in a previous writeup, so
$
  lim_(x->p) g(f(x)) = g(f(p)) = g(q) = r .
$

== (c)

As the counterexample shows, the result in (a) does not hold if only $f$ is continuous. But continuity of $g$ is enough:

#theorem[
  If $g: RR -> RR$ is continuous and $lim_(x->p) f(x) = q$ and $lim_(x->q) g(x) = r$, then
  $
    lim_(x->p) g(f(x)) = r .
  $
]
#proof[
  Since $f$ and $g$ are defined on all of $RR$, every point in $RR$ is a limit point of their domain. By continuity of $g$ at $q$, $lim_(x->q) g(x) = g(q) = r$.
  
  Let $B_(epsilon)(r)$ be any neighborhood of $r = g(q)$. Then by continuity of $g$, there's a neighborhood $B_(eta)(q)$ of $q$ such that $g(B_(eta)(q)) subset.eq B_(epsilon)(r)$. (Since $g$ is continuous, the _entire_ neighborhood gets mapped inside the $epsilon$-ball around $r$, including $x = q$.)

  And because $lim_(x->p) f(x) = q$, corresponding to the neighborhood $B_(eta)(q)$, there's a neighborhood $B_(delta)(p)$ of $p$ such that for every $x in B_(delta)(p)$ such that $x != p$, we have $f(x) in B_(eta)(q)$. But since $g$ maps every point in $B_(eta)(q)$ inside $B_(epsilon)(r)$, we have
  $
    g(f(x)) in B_epsilon(r) "whenever" x in B_(delta)(p), x != p .
  $
  In other words,
  $
    lim_(x->p) g(f(x)) = r .
  $
]

#remark[
  This proof goes through because $g$'s continuity means that _every_ point in a neighborhood around its input gets mapped into the target ball. That is where the proof would fail if all we knew was that $lim_(x->q) g(x) = r$.
]

= Problem 2: Contraction Mapping Theorem
(Exercise 4.3.11)

=== Proof idea

Speaking informally and intuitively, every application of the function $f$ only moves us a factor of $c$ away from where we were before. So we should be able to relate the iteration to terms in a geometric series.

To make this precise, apply the triangle inequality to the thing we need to bound for the Cauchy Criterion.

Apply the sequential characterization of continuity to $(y_n)$ to obtain that it's a fixed point.

== Proofs

Let $f: RR -> RR$ and $c$ a constant such that $0 < c < 1$ and
$
  abs(f(x) - f(y)) <= c abs(x-y)
$
for all $x, y in RR$.

== (a)

#theorem[
  $f$ is continuous on $RR$.
]
#proof[
  Let $a in RR$ be any point. Then $a$ is in the domain of $f$ since $f$ is defined on all of $RR$. Let $epsilon > 0$ be given and set $delta = epsilon/c$. Then, whenever
  $
    abs(x - a) < delta
  $ 
  we have
  $
    abs(f(x) - f(a)) <= c abs(x-a) < c delta = epsilon .
  $
  So $f$ is continuous at $a$. Since $a$ was arbitrary, $f$ is continuous on all of $RR$.
]

== (b)

#theorem[
  Let $y_1 in RR$ be any point and define the sequence $(y_n)$ by
  $
    y_(n+1) = f(y_n)
  $
  for $n >= 1$. Then $(y_n)$ is Cauchy.
]
#proof[
  Define
  $
    z_n = abs(y_n - y_(n-1))
  $
  for $n > 1$.

  Then by the given properties of the function $f$ and the definition of the sequence $(y_n)$,
  $
    z_n = & abs(y_n - y_(n-1)) \
        = & abs(f(y_(n-1)) - f(y_(n-2))) \
       <= & c abs(y_(n-1) - y_(n-2)) \
        = & c z_(n-1) 
  $
  for $n > 2$.

  So, when $n$ is large enough that all the $z_i$'s below are defined, we have
  $
    z_n <= c z_(n-1) <= c^2 z_(n-2) <= ... <= c^m z_(n-m) <= ... 
  $ <eq1>

  Let $epsilon > 0$ be given. To show that the sequence $(y_n)$ is Cauchy, we must find some $N in NN$ such that whenever $m > n >= N$ we have $abs(y_m - y_n) < epsilon$. To bound this quantity we add and subtract all $y_i$'s between $m$ and $n$, then apply the triangle inequality:
  $
    & abs(y_m - y_n) \
    = & abs(y_m - y_(m-1) + y_(m-1) - y_(m-2) + y_(m-2) - ... + y_(n+1) - y_n) \
   <= & abs(y_m - y_(m-1)) + abs(y_(m-1) - y_(m-2)) + ... + abs(y_(n+1) - y_n) \
    = & z_m + z_(m-1) + ... + z_(n+1) .
  $

  Here we apply @eq1 to bound each $z_i$ by a multiple of $z_(n+1)$:
  $
     & z_m + z_(m-1) + ... + z_(n+1) \
  <= & c^(m-n-1) z_(n+1) + c^(m-n-2) z_(n+1) + ... c z_(n+1) + z_(n+1) \
   = & z_(n+1) sum_(i=0)^(m-n-1) c^i \
  < & z_(n+1) frac(1,1-c)
  $
  where the last inequality follows because sum in the previous step is a partial sum of the geometric series $sum_(i=0)^infinity c^i$, and every term in this series is positive since $0 < c < 1$, and the series converges because $abs(c) < 1$.

  Now, the quantity $z_(n+1)$ itself may be bounded by another application of @eq1:
  $
    z_(n+1) <= c^(n-1) z_2 .
  $

  So
  $
    abs(y_m - y_n) < c^(n-1)/(1-c) z_2 .
  $

  Since $0 < c < 1$, we may choose $N$ so that
  $
    c^(N-1)/(1-c) z_2 < epsilon ;
  $
  such an $N$ is guaranteed to exist because the sequence $(c^n)$ converges to 0. (Why? I reproduce the proof in the book as review for myself: the sequence converges to some $l$ by the Monotone Convergence Theorem. $(c^(2n))$ is a subsequence that must converge to the same $l$. But $c^(2n) = c^n c^n$ so by the Algebraic Limit Theorem, $l^2 = l$, and $l$ cannot be $1$.)
]

Hence we may let $y = lim y_n$.

== (c)
#theorem[
  Let $y = lim y_n$. Then $y$ is a fixed point of $f$, that is,
  $
    y = f(y)
  $
]
#proof[
  We have proved that $f$ is continuous. By the Sequential Characterization of Continuity, since $(y_n) -> y$, we must have
  $
    (f(y_n)) -> f(y) .
  $
  But the sequence $(f(y_n))$ is $(f(y_1), f(y_2), ...)$, that is, the same as $(y_n)$ without the first term. So it is a subsequence, and must therefore converge to the same limit. So
  $
    (f(y_n)) -> y .
  $
  Limits of sequences are unique, so $y = f(y)$.
]

#theorem[
  There is a unique $y in RR$ such that
  $
    y = f(y)
  $
]
#proof[
  The preceding theorems demonstrate the existence of at least one $y$ such that $y = f(y)$.

  Suppose for the sake of contradiction that there existed distinct $x, y in RR$ satisfying $x = f(x)$ and $y = f(y)$. By the defining property of $f$,
  $
    abs(f(x) - f(y)) <= c abs(x - y) .
  $
  Substituting $x = f(x)$ and $y = f(y)$,
  $
    abs(x - y) <= c abs(x - y) .
  $
  Since $x != y$, the quantity $abs(x-y)$ is nonzero and so we may divide by it to obtain
  $
    c >= 1,
  $
  a contradiction of $0 < c < 1$.
]

== (d)
#theorem[
  If $x$ is any arbitrary point in $RR$, then the sequence $(x, f(x), f(f(x)), ...)$ converges to $y$ defined in part (b).
]
#proof[
  Let $(x_n)$ be the sequence $(x, f(x), f(f(x)), ...)$. Since $y_1$ in part (b) was arbitrary, the same proofs apply to $(x_n)$, so $(x_n)$ converges. Let $l = lim x_n$. Then by part (c), $l$ must satisfy $l = f(l)$. By the previous result, $l = y$.
]

= Problem 3: Uniform Continuity of $1 slash x^2$
(Exercise 4.4.3)

#theorem[
  $f(x) = 1 slash x^2$ is uniformly continuous on $[1, infinity)$.
]
#proof[
  Let $epsilon > 0$ be given and set $delta = min(1/2, epsilon/10)$.

  Let $x,c in [1, infinity)$ be any points in the given domain with $abs(x-c) < delta$. Then
  $
    c >= 1 \
    "so" \
    0 < 1/c <= 1.
  $

  We will need a bound for $abs(x+c)$ soon. Write $x+c = x + c - c + c = 2c + x - c$ and apply the triangle inequality to get
  $
    abs(x+c) <= 2 abs(c) + abs(x-c) = 2 c + delta 
  $
  so
  $
    abs(x+c)/abs(c) <= 2 + delta/c
  $

  Also, since $delta <= 1/2$ and $c >= 1$,
  $
    x > c - delta >= 1/2 \
    "so" \
    1/x < 2 .
  $

  So
  $
    abs(1/x^2 - 1/c^2) = abs((c^2 - x^2)/(c^2 x^2)) = abs((c-x)/(c x)) abs((c+x)/(c x)) .
  $

  Now we have bounds for every factor in this last expression:
  $
    abs(c-x) & < delta,\
    abs(1/c) & <= 1, \
    abs(1/x) & <= 2 text("(which appears twice)"), \
    abs(c+x)/abs(c) & <= 2 + delta/c <= 2 + delta,
    
  $
  which we multiply together to obtain
  $
    abs(1/x^2 - 1/c^2) < delta dot 2 dot 2 dot (2+delta) = 4 delta(delta + 2) .
  $

  Since $delta <= 1/2$ we have $delta + 2 <= 5/2$, so
  $
    4 delta(delta + 2) <= 10 delta <= epsilon 
  $
  as required.
]

#theorem[
  $f(x) = 1 slash x^2$ is not uniformly continuous on $(0, 1]$.
]
#proof[
  Define
  $
    x_n = cos(n/(n+1) pi/2) \
    "and" \
    y_n = cot(n/(n+1) pi/2) .
  $

  Let
  $
    theta_n = n/(n+1) pi/2 .
  $

  Then for every $n in NN$, since $theta_n in [pi/4, pi/2)$, both $cos theta_n$ and $cot theta_n$ are positive and at most 1. Hence, both $x_n$ and $y_n$ are in $(0, 1]$.

  Also,
  $
    abs(x_n - y_n) = abs(cos theta_n - cot theta_n) = abs(frac(cos theta_n (sin theta_n - 1), sin theta_n))
  $

  As $n -> infinity$,
  $
    theta_n -> pi/2
  $
  so by continuity of the sine and cosine functions and the sequential criterion of continuity,
  $
    cos theta_n -> 0, \
    sin theta_n -> 1, \
    sin theta_n != 0
  $
  so $abs(x_n - y_n) -> 0$ by the Algebraic Limit Theorem and continuity of the absolute value function.

  But
  $
    abs(f(x_n) - f(y_n)) = abs(1/x_n^2 - 1/y_n^2) = abs(sec^2 theta_n - tan^2 theta_n) = 1
  $
  for every $n$.

  Put $epsilon_0 = 1$ in the Sequential Criterion for Absence of Uniform Continuity. Then, since $abs(x_n - y_n) -> 0$ but $abs(f(x_n) - f(y_n)) = 1 >= epsilon_0$, the function $f(x) = 1 slash x^2$ fails to be uniformly continuous on $(0, 1]$.
]

#remark[
  This example is maybe a bit cheap since one could argue that all the hard work is happening in the definitions of the trigonometric functions and the proofs of their properties.
]

#remark[
  It feels like we should be able to figure out some properties of $1 slash x^2$ and the two domains, and prove theorems relating those properties to uniform continuity. Maybe something to do with being monotone? Or bounded vs unbounded?

  On $[1,infinity)$ the function is bounded and monotone (and continuous). Maybe that's enough to prove uniform continuity.

  On $(0, 1]$ the function is unbounded. Unboundedness is not enough to make a function not uniformly continuous, though. For example the identity function is unbounded, monotone, continuous and uniformly continuous on $[0, infinity)$.
]

#remark[
  Actually, maybe we can use the Continuous Extension Theorem from the next problem to say something like: $1 slash x^2$ is unbounded in every neighborhood of $x=0$, therefore it can have no continuous extension on any interval containing 0, therefore it is not uniformly continuous on $(0,1)$, therefore it is not uniformly continuous on $(0,1]$.
]

= Problem 4: Continuous Extension Theorem
(Exercise 4.4.13)

== (a)
#theorem[
  Suppose that $f: A -> RR$ is uniformly continuous and $(x_n) subset.eq A$ is a Cauchy sequence. Then $(f(x_n))$ is Cauchy.
]
#proof[
  Let $epsilon > 0$ be given. By uniform continuity of $f$ on $A$, there exists some $delta > 0$ such that for all $x, y in A$, whenever $abs(x-y) < delta$ we have $abs(f(x) - f(y)) < epsilon$.

  Since $(x_n)$ is Cauchy, there exists some $N in NN$ such that whenever $m > n >= N$, we have $abs(x_m - x_n) < delta$.

  Therefore whenever $m > n >= N$, since $abs(x_m - x_n) < delta$, we have $abs(f(x_n) - f(x_m)) < epsilon$, showing that $(f(x_n))$ is Cauchy.
]

== (b)

#theorem[
  Let $g$ be a continuous function on the open interval $(a,b)$. Then $g$ is uniformly continuous on $(a,b)$ iff it is possible to define values $g(a)$ and $g(b)$ at the endpoints so that the extended function $g$ is continuous on $[a,b]$.
]
#proof[
  ($=>$)
  We may assume $a != b$, otherwise the set $(a,b)$ is empty, $g$ takes no values there and there is nothing to prove.
  
  Suppose that $g$ is uniformly continuous on $(a,b)$. Then define the sequences
  $
    & x_n = a + (b-a)/(2n),\
    & y_n = b - (b-a)/(2n)
  $
  so that $(x_n) -> a$ and $(y_n) -> b$, and both sequences have all their terms in $(a,b)$. Since the sequences converge, they are Cauchy. Then by the previous result, $g(x_n)$ and $g(y_n)$ are also Cauchy, and therefore converge. Define $g(a) = lim g(x_n)$ and $g(b) = lim g(y_n)$.

  Define the function
  $
    h(x) = cases(
      g(x) "if" x in (a,b),
      g(a) "if" x = a,
      g(b) "if" x = b
    ) .
  $

  Let $(z_n) subset.eq [a,b]$ be any sequence converging to $a$ with $z_n != a$. Then after finitely many terms we must also have $z_n != b$, since $abs(b-a) > 0$ and all terms of $(z_n)$ must eventually be less than that distance from $a$. So after dropping that finite prefix and replacing $(z_n)$ by its tail, $(z_n) subset.eq (a,b)$.

  Then $(x_n - z_n) -> 0$ by the Algebraic Limit Theorem. Also, since $(z_n)$ is convergent, it is Cauchy, so by the previous theorem $(g(z_n))$ is Cauchy. Therefore it converges to some limit, call it $l$. Therefore $(g(x_n) - g(z_n)) -> g(a) - l$ by the Algebraic Limit Theorem.

  We claim that $(g(x_n) - g(z_n)) -> 0$: let $epsilon > 0$ be given. Then by uniform continuity of $g$ on $(a,b)$, there exists some $delta > 0$ such that $abs(x_n - z_n) < delta => abs(g(x_n) - g(z_n)) < epsilon$. By convergence of $(x_n - z_n)$ to 0, there exists some $N in NN$ such that when $n >= N$, $abs(x_n - z_n) < delta$. Therefore, for $n >= N$ we have $abs(g(x_n) - g(z_n)) < epsilon$, proving convergence to 0.

  Since limits of sequences are unique, we have $g(a) - l = 0$ so $l = g(a)$.

  Therefore, by the Sequential Criterion for Functional Limits, $lim_(x->a) h(x) = g(a)$. But then, since $a$ is a limit point of the domain of $h$, $[a,b]$, by Theorem 4.3.2 (Characterizations of Continuity) part (iv), we have $h(x)$ continuous at $a$.

  (This argument shows both that $g(a)$ is well-defined, and that $h(x)$ is continuous at $a$.)

  By a symmetric argument, $h(x)$ is continuous at $b$. Also, $h(x)$ is continuous at every point in $(a,b)$, i.e., adding endpoints doesn't matter there: since that region is open, for any $c in (a,b)$ there's a neighborhood of $c$ contained entirely in $(a,b)$ where $h$ and $g$ agree, so by continuity of $g$ on $(a,b)$ and using the $epsilon-delta$ definition of continuity, $h$ is continuous at every $c in (a,b)$.

  Therefore the extension is continuous on $[a,b]$.

  ($arrow.double.l$)

  Suppose that it is possible to define values $g(a)$ and $g(b)$ at the endpoints so that the extended function $g$ is continuous on $[a,b]$. Since the closed interval is compact, the extended $g$ is uniformly continuous on $[a,b]$.

  By the definition of uniform continuity, for every $epsilon > 0$ there exists a $delta > 0$ such that for all $x, y in [a,b]$, $abs(x-y) < delta$ implies $abs(g(x) - g(y)) < epsilon$. Since the condition holds for all $x, y in [a,b]$, it also holds for all $x, y in (a,b)$ or any other subset of $[a,b]$. So $g$ is uniformly continuous on $(a,b)$ as well.
]

#remark[
  I do a weird tricky thing here by using sequences that can't actually take on values at the endpoints, to prove continuity at the endpoints. To do this I had to go through the Functional Limit definition. It seems bad. I think the proof might be correct but I wonder if there's a clearer way to see it.
]

= Problem 5: Intermediate Value Theorem, Two Ways
(Exercise 4.5.5)

== (a) Using the Axiom of Completeness

#lemma[
  Let $f: [a,b] -> RR$ be continuous and $f(a) < 0 < f(b)$. Then $f(c) = 0$ for some $c in (a,b)$.
]
#proof[
  Define
  $
    K = {x in [a,b]: f(x) <= 0}.
  $

  Then $a in K$ since $f(a) < 0$, and $K$ is bounded above by $b$ since $K subset.eq [a,b]$ by construction. By the Axiom of Completeness, $K$ has a least upper bound. Let $c = sup K$. Then $c <= b$ since $b$ is an upper bound and $c$ the _least_ upper bound. So $f$ is continuous at $c$.

  By the ordering axioms, either $f(c) < 0$ or $f(c) > 0$ or $f(c) = 0$.

  If $f(c) > 0$ let $epsilon = f(c) > 0$. Then by continuity of $f$ at $c$, there exists some $delta > 0$ such that whenever $abs(x-c) < delta$ we have $abs(f(x) - f(c)) < epsilon$. So
  $
    -epsilon < f(x) - f(c) < epsilon    
  $
  so, since $epsilon = f(c)$,
  $
    f(x) > 0
  $
  for every $x in (c-delta,c+delta)$. But by the defining property of least upper bound, there must be some $alpha in K$ satisfying $c-delta < alpha < c$, a contradiction.

  If, on the other hand, $f(c) < 0$ then let $epsilon = -f(c) > 0$. By continuity of $f$ at $c$ there exists some $delta > 0$ such that whenever $abs(x-c) < delta$ we have $abs(f(x) - f(c)) < epsilon$. So
  $
    -epsilon < f(x) - f(c) < epsilon
  $
  so, since $epsilon = -f(c)$,
  $
    f(x) < 0
  $
  for every $x in (c-delta,c+delta)$. So $f(c+delta/2) < 0$, so $c+delta/2 in K$, so $c$ is not an upper bound for $K$.

  The only remaining possibility is that $f(c) = 0$.

  We now show that $c in (a,b)$. Since $a in K$ and $c = sup K$ we have $c >= a$. We previously showed that $c <= b$. But $f(c) = 0$ while $f(a) < 0 < f(b)$, so $c != a$ and $c != b$. Therefore $c in (a,b)$.
]

== (b) Using Nested Interval Property

#lemma[
  Let $f: [a,b] -> RR$ be continuous and $f(a) < 0 < f(b)$. Then $f(c) = 0$ for some $c in (a,b)$.
]
#proof[
  Let $I_0 = [a,b]$ and set $z_0 = (a+b)/2$, that is, its midpoint. If $f(z_0) >=0$ then set $a_1 = a$ and $b_1 = z_0$. Otherwise it must be that $f(z_0) < 0$, in which case set $a_1 = z_0$ and $b_1 = b$.

  Either way, the interval $I_1 = [a_1, b_1]$ has the property that $f(a_1) < 0$ and $f(b_1) >= 0$ and $"len"(I_1) = "len"(I_0) slash 2$ and $I_0 supset I_1$.

  Continuing in this way, form the sequence of intervals $I_0 supset I_1 supset I_2 supset ... supset I_n supset ...$. Then $"len"(I_k) = (b-a) slash 2^k$. By the Nested Interval Property, there exists a real number $c$ that's in every interval $I_k$.

  $f$ is continuous at $c$ since $c in I_0 = [a,b]$. Then by the ordering axioms, either $f(c) < 0$ or $f(c) > 0$ or $f(c) = 0$.

  If $f(c) > 0$ then let $epsilon = f(c) > 0$ in the definition of continuity. Then there must exist some $delta > 0$ such that $f(x) > 0$ for every $x$ in that neighborhood. But, by the Archimedean Principle, there's some $k in NN$ such that the length of $I_k$ is smaller than $delta$. Then, since $c in I_k$ and $"len"(I_k) < delta$, the entire interval $I_k subset.eq (c-delta,c+delta)$. So in particular its left endpoint $a_k in (c-delta, c+delta)$. By the construction of each $I_k$, at its left endpoint $f(a_k) < 0$, a contradiction.

  If $f(c) < 0$ then let $epsilon = -f(c) > 0$. By an exactly symmetric argument there's a neighborhood of $c$ where $f$ is always negative but an interval that fits inside at whose right endpoint $f(b_k) >= 0$, a contradiction.

  Therefore $f(c) = 0$. Since $c in [a,b]$ but $f(a) < 0 < f(b)$ we get $c != a$ and $c != b$. Therefore $c in (a,b)$.
]

== The rest of the theorem

#theorem[
  Let $f: [a,b] -> RR$ be continuous. If $L$ is a real number satisfying $f(a) < L < f(b)$ or $f(a) > L > f(b)$, then there exists a point $c in (a,b)$ where $f(c) = L$.
]
#proof[
  Suppose $f(a) < L < f(b)$. Then define
  $
    g(x) = f(x) - L .
  $
  Then $g$ is continuous by the Algebraic Continuity Theorem and satisfies
  $
    g(a) < 0 < g(b),
  $
  so by the preceding results there exists some $c in (a,b)$ such that $g(c) = 0$. Then $f(c) - L = 0$ so $f(c) = L$.

  Now suppose that $f(a) > L > f(b)$, so
  $
    -f(a) < -L < -f(b),
  $
  so
  $
    L - f(a) < 0 < L - f(b).
  $

  Define
  $
    g(x) = L - f(x)
  $
  which is continuous by the Algebraic Continuity Theorem. The inequality above shows that $g(a) < 0 < g(b)$, so there exists some $c in (a,b)$ such that $g(c) = 0$. Then $L - f(c) = 0$ so $f(c) = L$.
]

= Problem 6: A continuous $f: [0,1] -> [0,1]$ has a fixed point
(Exercise 4.5.7)

#theorem[
  Let $f$ be a continuous function on the closed interval $[0,1]$ with range also contained in $[0,1]$. Then $f$ has a fixed point, that is,
  $
    f(x) = x
  $
  for at least one value of $x in [0,1]$.
]
#proof[
  Consider
  $
    g(x) = f(x) - x .
  $

  By the Algebraic Continuity Theorem, $g(x)$ is continuous on $[0,1]$.

  The range of $f$ is contained in $[0,1]$, so $0 <= f(x) <= 1$ for every $x in [0,1]$. Therefore $g(0) = f(0) >= 0$, while $g(1) = f(1) - 1 <= 0$. That is,
  $
    g(0) >= 0 >= g(1) .
  $

  If $g(0) = 0$ or $g(1) = 0$ then we are done, for then the required point would be 0 or 1 respectively. Otherwise we may assume
  $
    g(0) > 0 > g(1) .
  $

  By the Intermediate Value Theorem, there exists a point $c in (0,1)$ such that $g(c) = 0$, i.e., $f(c) = c$.
]
