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

= Problem 1: In Hausdorff spaces, compact sets are closed
=== Proof idea

If a set has the property that every point in it contains a little open blob around it, with the open blob staying entirely inside the set, then the set is open: just take the union of the blobs.

We need to prove $K^c$ is open. If we take a point in the complement and a point in the set and apply the Hausdorff axiom, the rest follows.

The exercise is given right after the definitions of a topological space and a Hausdorff space. There's very little to work with, in some sense, so there are only a few "moves" to try. Obviously this is not helpful for solving problems in the wild.

== Proof

#lemma[
  Let $X$ be any topological space and $A subset.eq X$ a subset. If, for every $y in A$ there exists an open set $U_y$ such that $y in U_y$ and $U_y subset.eq A$, then $A$ is open.
]
#proof[
  Consider the set
  $
    B = union.big_(y in A) U_y .
  $

  Every element $y in A$ is contained in its corresponding $U_y$, so $y in B$.

  Every element $y in B$ is a member of some $U_y$, but every $U_y subset.eq A$. So $y in A$.

  By these inclusions, $A = B$. Since any union of open sets is open, $A$ is open.
]

#theorem[
  If $X$ is a Hausdorff space and $K subset.eq X$ is compact then $K$ is closed in $X$.
]
#proof[
  If $K^c$ is empty then it is open since the empty set is always open. Thus $K$ is closed and the theorem is proved.

  Otherwise let $y$ be any point in $K^c$. Since $X$ is Hausdorff, for each $x in K$ there exist disjoint open sets $O_x$ and $V_x$ such that $x in O_x$ and $y in V_x$. Then the collection ${O_x: x in K}$ is an open cover of $K$. By compactness of $K$ there's a finite subcover ${O_x_1, O_x_2, ..., O_x_n}$. Set
  $
    O = union.big_(i = 1)^n O_x_i .
  $
  By the definition of a subcover, $K subset.eq O$.

  For each $x_i$ there's a corresponding $V_x_i$ from the Hausdorff condition that contains $y$. Set
  $
    V = inter.big_(i = 1)^n V_x_i .
  $
  Then $V$ is the finite intersection of open sets, so it's open. Since $V subset.eq V_x_i$ for each $x_i$, $V inter O_x_i = emptyset$ for each $x_i$. So $V inter O = emptyset$. Since $K subset.eq O$, we have $V inter K = emptyset$. In other words, $V subset.eq K^c$. Thus $y in V$, an open subset of $K^c$. Since $y$ was arbitrary, we have shown that every point $y in K^c$ has an open set contained entirely within $K^c$, so by the lemma above, $K^c$ is open.
]

= Problem 2: Nonzero derivative in an interval $=>$ function is injective
Exercise 5.3.2 

#theorem[
  Let $f$ be differentiable on an interval $A$. If $f'(x) != 0$ on $A$ then $f$ is one-to-one on $A$.
]
#proof[
  Suppose for the sake of contradiction that $f$ is not one-to-one on $A$. Then there exist some $x,y in A$ with $x != y$ such that $f(x) = f(y)$. Without loss of generality let $x < y$. Since $f$ is differentiable on $A$, it is continuous on $[x,y]$ and differentiable on $(x,y)$. But then by the Mean Value Theorem,
  $
    f'(c) = frac(f(x) - f(y),x-y) = 0
  $
  for some $c in (x,y)$, a contradiction.
]

A counterexample to the converse is $f(x) = x^3$ which is one-to-one on all of $RR$ since $f'(x) != 0$ on $(-infinity, 0) union (0, infinity)$, leaving just one point that is not covered by the theorem above. But $f(0) = 0$, and $f(x) != 0$ when $x != 0$ since $x(x^2) = 0$ implies $x = 0$ by the field axioms. Also, $f(x) < 0$ when $x < 0$, while $f(x) > 0$ when $x > 0$, so $f(x) != f(y)$ if $x < 0 < y$.

Yet $f'(0) = 0$.
 
= Problem 3: Differentiable function vanishing on a convergent sequence
Exercise 5.3.4 

== (a)
#theorem[
  Let $f$ be differentiable on an interval $A$ containing zero, and let $(x_n)$ be a sequence in $A$ with $(x_n) -> 0$ and $x_n != 0$. If $f(x_n) = 0$ for all $n in NN$, then $f(0) = 0$ and $f'(0) = 0$.
]
#proof[
  Since $f$ is differentiable on $A$, it is continuous on $A$. Therefore
  $
    (x_n) -> 0
  $
  implies
  $
    (f(x_n)) -> f(0),
  $
  but $(f(x_n))$ is the constant sequence $(0, 0, ...)$ which converges to 0. Hence $f(0) = 0$.

  For each $x_n$ we have
  $
    frac(f(x_n) - f(0), x_n - 0) = 0
  $
  since $f(x_n) = 0$ for all $x_n$ and $f(0) = 0$. By differentiability of $f$ at zero, the limit
  $
    f'(0) = lim_(x->0) frac(f(x) - f(0), x - 0)
  $
  exists. And by the Sequential Criterion for Functional Limits applied to the difference quotient function, since $(x_n) subset.eq A$ is a sequence satisfying $(x_n) -> 0$ and $x_n != 0$,
  $
    lim_(x->0) frac(f(x) - f(0), x - 0) = lim_(n->infinity) frac(f(x_n) - f(0), x_n - 0) = 0 .
  $
  So $f'(0) = 0$.
]

#theorem[
  If, in addition to the above hypotheses, we have that $f$ is twice-differentiable at zero, then $f''(0) = 0$.
]
#proof[
  For each $x_n$ consider the intervals
  $
    I_n = cases(
      [0,x_n] & "if" x_n > 0,
      [x_n,0] & "if" x_n < 0
    ) \
    "and" \
    J_n = cases(
      (0, x_n) & "if" x_n > 0,
      (x_n, 0) & "if" x_n < 0
    ) .
  $

  Then $J_n subset.eq I_n subset.eq A$. Since $f$ is differentiable on $A$, it is continuous on $I_n$ and differentiable on $J_n$. Therefore by the Mean Value Theorem, there exists some $c_n in J_n$ such that
  $
    f'(c_n) = frac(f(x_n) - f(0), x_n - 0) = 0/x_n = 0
  $
  since $f(x_n) = f(0) = 0$.

  Since $(x_n) -> 0$ and since $c_n in [-abs(x_n), abs(x_n)]$, by the Squeeze Theorem we have $(c_n) -> 0$. Note, however, that $c_n != 0$ since $c_n in J_n$ while $0 in.not J_n$.

  Since $f''(0)$ exists, by the Sequential Criterion for Functional Limits we have
  $
    f''(0) = lim_(x -> 0) frac(f'(x) - f'(0), x - 0) = lim_(n->infinity) frac(f'(c_n) - f'(0), c_n - 0) = lim_(n->infinity) frac(0 - 0, c_n) = 0
  $
  since $f'(c_n) = f'(0) = 0$, and $(c_n) -> 0$, and $c_n != 0$.
]

= Problem 4: Cauchy's Generalized Mean Value Theorem and its geometric interpretation
Exercise 5.3.5. 

== (a)
#theorem[
  If $f$ and $g$ are continuous on the closed interval $[a,b]$ and differentiable on the open interval $(a,b)$, then there exists a point $c in (a,b)$ where
  $
    [f(b) - f(a)]g'(c) = [g(b) - g(a)]f'(c) .
  $<eq4>

  If $g'$ is never zero on $(a,b)$, then the conclusion can be stated as
  $
    frac(f'(c), g'(c)) = frac(f(b) - f(a), g(b) - g(a)) .
  $<eq5>
]
#proof[
  Define
  $
    h(x) = [f(b) - f(a)]g(x) - [g(b) - g(a)]f(x) .
  $

  Some algebra reveals that $h(a) = f(b)g(a) - g(b)f(a) = h(b)$.

  Since it is the linear combination of $f$ and $g$, by the Algebraic Differentiability and Continuity Theorems, $h$ is continuous on $[a,b]$ and differentiable on $(a,b)$. Therefore by Rolle's Theorem there exists some $c in (a,b)$ where $h'(c) = 0$. Applying the Algebraic Differentiability Theorem leads to the desired @eq4.

  If, in addition, we are given that $g'(x) != 0$ for $x in (a,b)$ then $g(b) != g(a)$. I will repeat the argument from Problem 2 since it is quick: suppose $g(b) = g(a)$. Then by the Mean Value Theorem, for some $d in (a,b)$ we have
  $
    g'(d) = frac(g(b) - g(a), b - a) = 0,
  $
  a contradiction. Thus $g(b) - g(a) != 0$ and we may divide @eq4 by $g'(c)$ and $g(b) - g(a)$ to obtain @eq5.
]

== (b)

Consider the parameterized curve
$
  (g(t), f(t))
$
in the 2D cartesian plane. Cauchy's Generalized MVT says for any secant line connecting two points on this curve, there's some point between the endpoints where the tangent to the curve is parallel to the secant line.

Visually this looks exactly like the regular MVT, but the curves can be weirder (e.g., $(cos t, sin t)$, which cannot be represented by an ordinary function).

Algebraically, suppose the interval is $[a,b]$. Then the change in the $x$ coordinate is $g(b) - g(a)$ and the change in the $y$ coordinate is $f(b) - f(a)$ so the slope of the secant line is
$
  frac(f(b) - f(a), g(b) - g(a)) .
$

The slope of the tangent at any point $c$ is, uhh, I'll put on my physics hat for second,
$
  (dif y)/(dif x) = (dif y)/(dif t) dot (dif t)/(dif x) = ((dif y)/(dif t))/((dif x)/(dif t)) = f'/g',
$
evaluated at $c$. This does not constitute a proof but is certainly suggestive.

Maybe closer to a proof is: the slope of the tangent at some point $c$ is the limit, as $h->0$, of
$
  frac(f(t+h) - f(t), g(t+h) - g(t))
$
since that's the instantaneous rise over run. If we divide and multiply by $h$ we can probably get that to $f'(c)/g'(c)$.

= Problem 5: Bounds on derivatives $=>$ bounds on the function
Exercise 5.3.6

=== Proof idea

It would be nice to return to this problem once we study integration, the Fundamental Theorem of Calculus and some kind of triangle inequality generalization.

The main idea in this proof is that in some sense Cauchy's Generalized MVT allows us to compare two functions. The relevant functions to compare against here are $f(x) = x^2$ and $f(x) = x^3$ because, intuitively, we want to integrate the inequality 2 or 3 times.

Of course we can't actually integrate yet. Another connection here is Taylor's theorem: if this function were smooth (which it's not; this result is more general) then what would the expansion look like at 0? None of that is precise but it suggests comparing against polynomials.

I spent a lot of time trying to get the factor of $1/2$ using the (regular) Mean Value Theorem.

== (a)

#theorem[
  Let $g: [0,a] -> RR$ be differentiable, $g(0) = 0$, and $abs(g'(x)) <= M$ for all $x in [0,a]$. Then $abs(g(x)) <= M x$ for all $x in [0,a]$.
]
#proof[
  When $x = 0$ the theorem is trivial, since $abs(g(0)) = 0 <= M dot 0 = 0$.
  
  For every $x in (0,a]$, applying the Mean Value Theorem to the interval $[0,x]$, we have
  $
    frac(g(x) - g(0), x - 0) = frac(g(x),x) = g'(c)
  $
  for some $c in (0,x)$. Taking the absolute value of both sides,
  $
    frac(abs(g(x)), abs(x)) = abs(g'(c)) .
  $
  Since $x > 0$, $abs(x) = x$. And by the hypotheses, the right hand side is bounded by $M$. Thus,
  $
    abs(g(x)) <= M x .
  $
]

The bound is tight: $f(x) = M x$ achieves it.

== (b)

#theorem[
  Let $h: [0,a] -> RR$ be twice-differentiable, $h'(0) = h(0) = 0$ and $abs(h''(x)) <= M$ for all $x in [0,a]$. Then $abs(h(x)) <= M x^2 slash 2$ for all $x in [0,a]$.
]
#proof[
  When $x = 0$ the theorem is trivial, since $abs(h(0)) = 0 <= M dot 0^2 slash 2 = 0$.
  
  $h'$ satisfies the hypotheses of the theorem above, so
  $
    abs(h'(x)) <= M x
  $ <eq2>
  for all $x in [0,a]$. Fix some $x in (0,a]$. We now apply Cauchy's Generalized Mean Value Theorem to the functions $h$ and $t mapsto t^2$ (whose derivative is nonzero on $(0,x)$) on the interval $[0,x]$ to obtain the existence of some $c in (0,x)$ such that
  $
    frac(h'(c),2c) = frac(h(x) - h(0), x^2 - 0^2) = frac(h(x), x^2) .
  $
  Taking absolute values and using @eq2 and the fact that $c > 0$ we obtain
  $
    frac(abs(h(x)), x^2) = frac(abs(h'(c)), 2c) <= frac(M c, 2c) = M/2
  $
  and the result follows.
]

The bound is tight: $f(x) = M x^2 slash 2$ achieves it.

== (c)

#theorem[
  Let $h: [0,a] -> RR$ be thrice-differentiable, $h''(0) = h'(0) = h(0) = 0$ and $abs(h'''(x)) <= M$ for all $x in [0,a]$. Then $abs(h(x)) <= M x^3 slash 6$ for all $x in [0,a]$.
]
#proof[
  When $x = 0$ the theorem is trivial.

  $h'$ satisfies the hypotheses of the theorem above, so
  $
    abs(h'(x)) <= M x^2 slash 2
  $ <eq3>
  for all $x in [0,a]$. Fix some $x in (0,a]$. We now apply Cauchy's Generalized Mean Value Theorem to the functions $h$ and $t mapsto t^3$ (whose derivative is nonzero on $(0,x)$) on the interval $[0,x]$ to obtain the existence of some $c in (0,x)$ such that
  $
    frac(h'(c), 3c^2) = frac(h(x) - h(0), x^3 - 0^3) = frac(h(x), x^3) .
  $
  Taking absolute values and using @eq3 and the fact that $c > 0$ we obtain
  $
    frac(abs(h(x)), x^3) = frac(abs(h'(c)), 3c^2) <= frac(M c^2 slash 2, 3 c^2) = M/6
  $
  and the result follows.
]

The bound is tight: $f(x) = M x^3 slash 6$ achieves it.

Of course by induction we see that if a function $h$ and its first $n-1$ derivatives vanish at 0, and its $n$'th derivative is bounded by $M$, then
$
  h(x) <= (M x^n)/n!
$
for $x in [0,a]$.

= Problem 6: The $0 slash 0$ case of L'Hospital's Rule
Exercise 5.3.11 

== (a)

#theorem[
  Let $f$ and $g$ be continuous on an interval $A$ containing $a$, and assume $f$ and $g$ are differentiable on this interval with the possible exception of the point $a$. If $f(a) = g(a) = 0$ and $g'(x) != 0$ for all $x != a$ then
  $
    lim_(x->a) f'(x)/g'(x) = L wide "implies" wide lim_(x->a) f(x)/g(x) = L .
  $
]
#proof[
  Let $(b_n) subset.eq A$ be any sequence with $b_n != a$ and $(b_n) -> a$. Define the interval
  $
    I_n = cases(
      (a,b_n) wide & "if" b_n > a,
      (b_n,a) wide & "if" b_n < a
    ) .
  $

  By Cauchy's Generalized Mean Value Theorem, there exists some $c_n in I_n$ such that
  $
    (f'(c_n))/(g'(c_n)) = frac(f(b_n) - f(a), g(b_n) - g(a)) = f(b_n)/g(b_n)
  $
  where we may use this form of the theorem since $g'(x) != 0$ for all $x != a$, and consequently $g(b_n) != g(a)$ by the (regular) Mean Value Theorem.

  Since $c_n$ is always between $a$ and $b_n$, we have $0 < abs(c_n - a) < abs(b_n - a) -> 0$, so $(c_n) -> a$.

  Suppose that
  $
    lim_(x->a) (f'(x))/(g'(x)) = L.
  $

  Then by the Sequential Criterion for Functional Limits, since $(c_n) subset.eq A$ and $c_n != a$ and $(c_n) -> a$, we have
  $
    ((f'(c_n))/(g'(c_n))) -> L,
  $
  so the sequence
  $
    (f(b_n)/g(b_n)) -> L
  $
  as well, since every term of this sequence equals that of the convergent sequence $((f'(c_n))/(g'(c_n)))$.

  Since the sequence $(b_n)$ was arbitrary and satisfied $b_n != a$ and $(b_n) -> a$, by the Sequential Criterion for Functional Limits,
  $
    lim_(x->a) f(x)/g(x) = L .
  $
]

== (b)

Yes, if we keep the first part of the hypothesis the same but assume that
$
  lim_(x->a) (f'(x))/(g'(x)) = infinity
$
then it is the case that
$
  lim_(x->a) f(x)/g(x) = infinity .
$

The same proof as above goes through, but with every instance of $L$ replaced with $infinity$. To make this work we need to patch up the proof of the Sequential Criterion for Functional Limits to cover the $infinity$ case:

#theorem[
  Given a function $f: A -> RR$ and a limit point $c$ of $A$, the following two statements are equivalent:

  (i) $lim_(x->c) f(x) = infinity$

  (ii) For all sequences $(x_n) subset.eq A$ satisfying $x_n != c$ and $(x_n) -> c$, it follows that $f(x_n) -> infinity$.
]
#proof[

  ($=>$)

  Assume that $lim_(x->c) f(x) = infinity$ and let $(x_n)$ be an arbitrary sequence with $x_n != c$ and $(x_n) -> c$. Let $M > 0$ be given. By the definition of infinite limit, there exists some $delta > 0$ such that for every $x in V_(delta)(c) backslash {c}$ we have $f(x) > M$. But since $(x_n) -> c$, there exists some $N in NN$ such that whenever $m >= N$ we have $x_m in V_(delta)(c) backslash {c}$. Therefore whenever $m >= N$ we have $f(x_m) > M$ as desired.

  ($arrow.l.double$)

  We prove the contrapositive. Suppose that $lim_(x->c) f(x) != infinity$. Then there exists some $M > 0$ for which no $delta$ is a suitable response. That is, for every $delta > 0$ there exists some $x in V_(delta)(c) backslash {c}$ such that $f(x) <= M$. Then let $delta_n = 1 slash n$. From the preceding discussion it follows that for each $n in NN$ there exists some $x_n in V_(delta_n)(c) backslash {c}$ such that $f(x_n) <= M$. We have thus constructed a sequence $(x_n) -> c$ with $x_n != c$ where $(f(x_n)) arrow.not infinity$, and the proof is complete.
]
