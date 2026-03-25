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

= Problem 1: The derivative of $f slash g$
Exercise 5.2.3

== (a)
Let $h(x) = 1/x$. Then
$
  h'(c) = lim_(x->c) frac(1/x - 1/c,x-c) = lim_(x->c) frac(c-x,(x-c) c x) = lim_(x->c) frac(-1, c x).
$

By the Algebraic Limit Theorem, when $c!=0$ this converges to $-1/c^2$. So $h$ is differentiable on $RR backslash {0}$

== (b)
Let $f: A -> RR$ and $g: A -> RR$ be defined on an interval $A$ and be differentiable at $c in A$.

First we find the derivative of $1 slash g(x)$ using the Chain Rule:

Let $h(x) = 1 slash x$. Then $(h compose g)(x) = 1 slash g(x)$. By the Chain Rule, since $h$ is differentiable except at $x = 0$,
$
  (frac(1,g))'(c) = (h compose g)'(c) = h'(g(c)) g'(c) = frac(-g'(c), [g(c)]^2)
$
whenever $g(c) != 0$.

Now we apply the part (iii) of the Algebraic Differentiability Theorem to find the derivative of the product:
$
  (f slash g)' = (f dot 1 slash g)'
$
so
$
  (f slash g)'(c) = f(c)(frac(-g'(c), [g(c)]^2)) + frac(f'(c),g(c))
$
which simplifies to
$
  frac(f'(c)g(c) - g'(c)f(c), [g(c)]^2),
$
valid when $g(c) != 0$.

== (c)

Let us rewrite the numerator of the difference quotient like so:
$
  & f(x)/g(x) - f(c)/g(c) \
  = & frac(f(x)g(c) - g(x)f(c), g(x)g(c)) \
  = & frac(f(x)g(c) - f(c)g(c) + f(c)g(c) - g(x)f(c), g(x)g(c))
$
where we added and subtracted $f(c) g(c)$ in the final step. Next we will group the first pair and the second pair by factoring out a common $g(c)$ and $f(c)$ respectively.

So
$
  & lim_(x->c) frac(f(x) slash g(x) - f(c) slash g(c), x - c) \
  = & lim_(x->c) frac(1,g(x)g(c)) dot lim_(x->c) frac(g(c)[f(x) - f(c)] - f(c)[g(x)-g(c)],x-c).
$
The first limit evaluates to $1 slash [g(c)]^2$ by continuity of $g$ (since it is given to be differentiable). By the Algebraic Limit Theorem, we may pull out the constants $g(c)$ and $f(c)$. Then by the definition of the derivative we obtain, for the whole expression,
$
  frac(1,[g(c)]^2) dot (g(c) f'(c) - f(c) g'(c))
$
as desired.

= Problem 2: A parameterized family of functions, good for manufacturing examples related to the existence and continuity of derivatives of various orders
Exercise 5.2.7

Let
$
  g_(a)(x) = cases(
    x^a sin(1 slash x) & "if" x != 0,
    0                  & "if" x = 0
  )
$

=== Proof idea

The main ideas in this problem:
- Return to the definition of the derivative to find out what's happening at zero
- When we need a fractional power, be careful of square roots since they don't exist for negative inputs. But cube roots do!

One interesting thing that this problem made me think about: just because $x^(-1/3)$ is unbounded doesn't mean $cos(1/x) x^(-1/3)$ is also unbounded: what if $cos(1/x)$ is zero exactly where $x^(-1/3)$ blows up? But the definition of $lim_(x->c) f(x) = infinity$ shows that this can't happen: for any $M$, we must have $f(x) > M$ for _every_ $x$ such that $abs(x-c) < delta$. So we can take the values of $x$ where $cos(1/x) = 1$ to convince ourselves that the product is also unbounded.

So, for a function's limit to be infinity is a stronger condition than for it to be unbounded.

== (a)

We want $g_(a)$ to be differentiable on $RR$ but $g'_(a)$ to be unbounded on $[0,1]$. Let us compute the derivative:

Away from 0 we can use Chain Rule, Algebraic Differentiability Theorem, results about derivatives of the trigonometric functions, and the power rule for fractional powers (we haven't proved these last two but I don't see a way to do this problem without them) to obtain:
$
  g'_(a) = a x^(a-1) sin(1 slash x) - x^(a-2) cos(1 slash x) .
$

This is unbounded near 0 when $a < 2$, because $x^(a-2)$ is then unbounded, as shown by the sequence $y_n = 1 slash 2 pi n$.

At 0 we use the definition of derivative:
$
  g'_(a)(0) = lim_(x->0) frac(x^a sin(1 slash x) - 0, x-0) = lim_(x->0) x^(a-1) sin(1 slash x) .
$

When $a > 1$, this converges to 0 since $abs(sin(1 slash x)) <= 1$ but $x^(a-1) -> 0$. When $a=1$ it oscillates indefinitely so there is no derivative at 0. For $a < 1$ it is unbounded near $0$, so there is no derivative at 0.

So we'll need $a > 1$ for the function to be differentiable on all of $RR$.

To satisfy both conditions we need $1 < a < 2$. We also need $x^a$, $x^(a-1)$ and $x^(a-2)$ to be defined for negative real numbers. So $a$ must be a rational number with odd denominator.

Set $a=5/3$. Then the derivative at 0 is 0. Elsewhere the derivative is
$
  g'_(5 slash 3)(x) = 5/3 x^(2 slash 3)sin(1 slash x) - frac(1,x^(1 slash 3)) cos(1 slash x) .
$

This exists on all of $RR backslash {0}$. The first term stays bounded, while the second is unbounded near zero. To prove this we exhibit the sequence
$
  y_n = frac(1,2 pi n) .
$

Let $f(x) = x^(-1 slash 3) cos(1 slash x)$. Then $f(y_n) = (2 pi n)^(1 slash 3)$, so $f(y_n) -> infinity$.

== (b)

We want $g_a$ differentiable on all of $RR$, with $g'_(a)$ continuous but not differentiable at 0.

By the previous part, for $g_a$ to be differentiable on $RR$ we need $a > 1$.

For $g'_(a)$ to be continuos at 0, we need $a > 2$ so that the very term we wanted to blow up last time, $x^(a-2) cos(1 slash x)$, goes to 0 instead.

For the differentiability of $g'_(a)$ at 0, we use the definition:
$
  g''_(a)(0) = & lim_(x->0) frac(a x^(a-1) - x^(a-2) cos(1 slash x) - 0,x-0) \
  = & lim_(x->0) [a x^(a-2) sin(1 slash x) - x^(a-3) cos(1 slash x)] .
$

When $a > 3$ this converges to 0. When $a = 3$, the $cos(1 slash x)$ oscillates. And when $a < 3$ the term $x^(a-3) cos (1 slash x)$ goes to infinity.

So by picking $a = 3$ we satisfy all the conditions we want:
- $g_a$ differentiable on all of $RR$
- $g'_a$ continuous at 0
- but $g'_a$ not differentiable at 0, because the limit does not exist due to the oscillations of $cos(1 slash x)$ in every neighborhood of 0.

== (c)

From the previous part, we know $g''_a(0) = 0$ when $a > 3$. To analyze its continuity we compute $g''_(a)$ away from 0 using the usual rules of differentiation:
$
  g''_(a)(x) = & a(x^(a-1) sin(1 slash x))' - [x^(a-2) cos(1 slash x)]' \
  = & a(a-1) x^(a-2) sin(1 slash x) - a x^(a-3) cos(1 slash x) - x^(a-4) sin(1 slash x) - (a-2) x^(a-3) cos(1 slash x) .
$

The only term that matters here is $x^(a-4)sin(1 slash x)$. When $a=4$, this term becomes $sin(1 slash x)$ which oscillates indefinitely and doesn't converge to 0 as $x->0$.

We want:
- $g_a$ differentiable on all of $RR$. That happens when $a > 1$.
- $g'_a$ differentiable on all of $RR$. That happens when $a > 3$.
- But $g''_a$ not continuous at 0. Setting $a=4$ accomplishes this.

So $a=4$ does the job.

= Problem 3: Discontinuities of derivatives
Exercise 5.2.9

=== Proof idea

For part (a): since derivatives have the Intermediate Value Property, the set of values $f'(x)$ takes as $x$ varies over an interval is itself an interval. And any interval with more than one value has both rationals and irrationals.

For part (b): if derivatives were always continuous then this would be true. But they are not. So any counterexample must involve a discontinuous derivative. In Problem 2 we met such a family.

For part (c): derivatives can't have jump discontinuities, only wild oscillations. But if the limit exists we can't have wild oscillations. So the statement must be true, and to prove it we must use a theorem which gets at the fact that derivatives can't have jump discontinuities. Both Darboux's Theorem and the Mean Value Theorem get at this property.

For the proof by Darboux's Theorem, we want a contradiction where everything in a neighborhood must be within some $epsilon$ of $L$, but Darboux's Theorem says that $f'$ must take on an intermediate value (I pick the average of $f'(0)$ and some value in the neighborhood) that's too far away from $L$.

== (a)

#theorem[
  If $f'$ exists on an interval and is not constant, then $f'$ must take on some irrational values.
]
#proof[
  Let $f'$ exist on an interval $[a,b]$ and not constant. Then $f'(c) != f'(d)$, for some $c,d in [a,b]$. So there exist real numbers between $f'(c)$ and $f'(d)$. By density of the irrationals in $RR$, there exists some irrational number $p$ between them. By Darboux's Theorem, $f'(e) = p$ for some $e$ between $c$ and $d$.
]

== (b)

The following statement is false: If $f'$ exists on an open interval and there is some point $c$ where $f'(c) > 0$, then there exists a $delta$-neighborhood $V_(delta)(c)$ around $c$ in which $f'(x) > 0$ for all $x in V_(delta)(c)$.

Counterexample:
$
  h(x) = cases(
    x^2 sin(1 slash x) + x slash 2 & "if" x != 0,
    0                              & "if" x = 0
  )
  
$

Then $h(x) = g_(2)(x) + x slash 2$, where $g_a$ is the function from Problem 1 (since $x slash 2 = 0$ at $x = 0$). As we showed in that problem, $g'_2(0) = 0$, so by the Algebraic Differentiation Theorem, $h'(0) = 1 slash 2$.

But away from 0,
$
  h'(x) = & g'_2(x) + 1 slash 2 \
  = & 2 x sin(1 slash x) - cos(1 slash x) + 1 slash 2
$
which takes on negative values in every neighborhood of zero as shown by the sequence
$
  y_n = frac(1,2 pi n)
$
where
$
  h'(y_n) = & 2/(2 pi n) sin(2 pi n) - cos(2 pi n) + 1 slash 2 \
  = & 0 - 1 + 1 slash 2 \
  = & -1 slash 2
$
for every $n$.

== (c)

#theorem[
  If $f$ is differentiable on an interval containing zero and if $lim_(x->0) f'(x) = L$, then it must be that $L = f'(0)$.
]
#proof[
  Let $f'(0) = M$, which exists since $f$ is differentiable on the entire interval containing zero.

  Suppose for the sake of contradiction that $M != L$. Then let $epsilon = abs(M - L)/3 > 0$.

  Since $lim_(x->0) f'(x) = L$, there exists some $delta$-neighborhood $V_(delta)(0)$ of 0 such that $abs(f'(x) - L) < epsilon$ whenever $x in V_(delta)(0)$ and $x != 0$.

  Let $q$ be some point with $0 < q < delta$ and let $p = f'(q)$. Then $p$ is within $epsilon$ of $L$:
  $
    abs(p-L) < epsilon.
  $

  The interval $(0,q) subset.eq V_(delta)(0) backslash {0}$, so for every $x in (0,q)$, we have $abs(f'(x) - L) < epsilon$. But by Darboux's Theorem, since $f'(0) = M$ and $f'(q) = p$, for some $c in (0,q)$ we have $f'(c) = (M+p)/2$. We will show that by our choice of $epsilon$,
  $
    abs((M+p)/2 - L) > epsilon,
  $
  contradicting that $abs(f'(c) - L) < epsilon$ when $c in (0,q) subset.eq V_(delta)(0) backslash {0}$.

  To see this, we write
  $
    & M - L \
    = & M - L + (p-L) - (p-L) \
    = & (M+p-2L) - (p-L)
  $
  and apply the triangle inequality to obtain
  $
    abs(M-L) <= abs(M+p-2L) + abs(p-L) .
  $

  Since $abs(p-L) < epsilon$, we get
  $
    abs(M-L) < abs(M+p-2L) + epsilon,
  $
  so
  $
    abs(M+p-2L) > abs(M-L) - epsilon .
  $

  Dividing throughout by 2, we get
  $
    abs((M+p)/2 - L) > frac(abs(M-L) - epsilon,2) = frac(3 epsilon - epsilon,2) = epsilon,
  $
  which is the desired contradiction.
]

I happened to read the next section, so here's a proof using the Mean Value Theorem. Apologies for being pedantic; the proof is quite easy so I wanted to make sure I wasn't accidentally overlooking the true difficulty.

#proof[
  $f$ is differentiable on some interval containing 0. Pick any $a,b$ in the interval satisfying $a < 0 < b$. Then $f$ is differentiable on the interval $[a,b]$. Consider the sequence
  $
    a_n = a/n .
  $
  Then $a_n < 0$ for all $n$ and $(a_n) -> 0$. For every $n$, the interval $[a_n, 0]$ is contained in $[a,b]$, so $f$ is differentiable on $[a_n, 0]$. As a consequence, it is continuous on $[a_n, 0]$ and differentiable on $(a_n, 0)$. So by the Mean Value Theorem, for every $n$ there exists some $c_n in (a_n, 0)$ such that
  $
    f'(c_n) = (f(0) - f(a_n))/(0-a_n) = (f(a_n) - f(0))/(a_n - 0) .
  $<eq1>

  We apply the Sequential Criterion for Functional Limits to the left hand side, with the sequence $c_n$. For my own sake I will explicitly state the preconditions: let the domain of $f$ be $[a,b]$ for the purpose of applying the theorem. Then 0 is a limit point of $[a,b]$ since every element of an interval is a limit point; we are given that $lim_(x->0) f'(x) = L$; the sequence $(c_n) subset.eq [a,b]$; $c_n != 0$ since $c_n in (a_n, 0)$; and $c_n -> 0$ by the Order Limit Theorem since $a_n < c_n < 0$ and $a_n -> 0$.

  So the left hand side of @eq1 converges to $L$.

  For the right hand side, let
  $
    g(x) = (f(x) - f(0))/(x - 0) .
  $
  Since $f$ is differentiable on all of $[a,b]$, in particular it is differentiable at zero. Therefore the functional limit $lim_(x->0) g(x)$ exists and is equal to $f'(0)$, since that is just the definition of the derivative at zero.

  We now apply the Sequential Criterion for Functional Limits to the right hand side of @eq1, with the sequence $a_n$. Let the domain of $g$ be $[a,b] backslash {0}$ for the purpose of applying the theorem. Then 0 is a limit point of the domain; we have shown that $lim_(x->0) g(x) = f'(0)$; the sequence $(a_n) subset.eq [a,b] backslash {0}$; $a_n != 0$ for all $n$; and $(a_n) -> 0$. Therefore the right hand side of @eq1 converges to $f'(0)$.

  We have shown that
  $
    f'(c_n) = g(a_n)
  $
  for every $n$; that the sequence $(f'(c_n)) -> L$; and that the sequence $(g(a_n)) -> f'(0)$. Since limits are unique,
  $
    f'(0) = L
  $
  as desired.
]

= Problem 4: Positive derivative at a single point does not imply that the function is increasing
Exercise 5.2.10

=== Proof idea

The function wiggles up and down around the line $y=x slash 2$, and while the wiggles get tiny they never quite stop. So just exhibit two sequences that catch the sequence at the crests and middles of the wiggles.

My takeaway from this exercise is that if the derivative at a point $c$ is strictly positive, then for nearby points $x>c$ we have $f(x) > f(c)$ and for nearby points $y < c$ we have $f(y) < f(c)$.

== Proof

In Problem 3 part (b), where this function was called $h$ instead of $g$, we showed that $g'(x)$ exists everywhere and that $g'(0) = 1 slash 2 > 0$.

Now consider the sequences
$
  a_n = 1/(2 pi n)
$
and
$
  b_n = 1/(pi/2 + 2 pi n)
$.

Both these sequences converge to 0, so every neighborhood of zero has infinitely many terms of both sequences.

We claim that $a_n > b_n$ for every $n$, because $a_n > 0$ and $b_n > 0$, so
$
  1/b_n = pi/2 + 1/a_n > 1/a_n
$
implies that $a_n > b_n$.

But $g(b_n) > g(a_n)$ for every $n$. To show this we compute
$
  g(b_n) - g(a_n) & = b_n/2 + b_n^2sin(1/b_n) - a_n/2 - a_n^2sin(1/a_n) \
  & = b_n/2 + b_n^2 - a_n/2
$
since $sin(pi/2 + 2pi n) = 1$ and $sin(2pi n) = 0$ for every $n in NN$.

This becomes
$
  & 1/(2pi n + pi/2)^2 - 1/(8n(2pi n + pi/2)) \
  = & (1/(2pi n + pi/2)) frac(8n - 2pi n - pi/2,8n(2pi n + pi/2)) .
$

The sign of this is the sign of the numerator, $8n - 2pi n - pi/2$. By direct numerical calculation it turns out that $8-2pi > pi/2 > 0$. So for $n >= 1$ we have
$
  n(8 - 2pi) > 8 - 2pi > pi/2,
$
hence
$
  n(8 - 2pi) - pi/2 > 0.
$

So in any open interval $A$ containing 0 there exists some $n$ such that both $a_n in A$ and $b_n in A$, and as we have shown, $a_n > b_n$ but $g(a_n) < g(b_n)$. So $g$ is not increasing in any open interval containing zero.

= Problem 5: Darboux's Theorem
Exercise 5.2.11

=== Proof idea

By compactness the function has a minimum on the closed interval. From the definition of the derivative and the given signs, the minimum can't happen at either endpoint. Then use the Interior Extremum Theorem.

== Proof

#theorem[
  If $f$ is differentiable on an interval $[a,b]$, and if $alpha$ satisfies $f'(a) < alpha < f'(b)$ (or $f'(a) > alpha > f'(b)$), then there exists a point $c in (a,b)$ where $f'(c) = alpha$.
]
#proof[
  We will prove the theorem for $f'(a) < alpha < f'(b)$; the other case is exactly symmetric or follows by applying the first case to $-f(x)$.

  Define
  $
    g(x) = f(x) - alpha x
  $
  on $[a,b]$. Then by the Algebraic Differentiability Theorem, $g(x)$ is differentiable on $[a,b]$ with $g'(x) = f'(x) - alpha$. Then $g'(a) < 0 < g'(b)$.

  First we show the existence of points $x_a, y_b in (a,b)$ such that $g(x_a) < g(a)$ and $g(y_b) < g(b)$:

  By differentiability of $g$ at $a$ and taking $epsilon = -g'(a) > 0$ in the definition of the derivative, there exists some $delta_a > 0$ such that whenever $0 < abs(x-a) < delta_a$ and $x in [a,b]$ we have
  $
    abs(frac(g(x) - g(a), x - a) - g'(a)) < epsilon
  $
  so
  $
    -epsilon < frac(g(x) - g(a), x - a) - g'(a) < epsilon .
  $

  Taking the second of these inequalities and substituting our choice of $epsilon = -g'(a)$, we get
  $
    frac(g(x) - g(a), x - a) < 0 
  $

  whenever $x in [a,b]$ and $0 < abs(x-a) < delta_a$. Let $x_a$ be any such $x$. (For example, we could set $x_a = a + min(delta_a,b-a) slash 2$). Then, since $x_a > a$ we may multiply both sides of the inequality by $x_a-a$ to get
  $
    g(x_a) < g(a) .
  $

  Similarly, by differentiability of $g$ at $b$ and taking $epsilon = g'(b) > 0$ in the definition of the derivative, there exists some $delta_b > 0$ such that whenever $0 < abs(y-b) < delta_b$ and $y in [a,b]$ we have
  $
    -epsilon < frac(g(y) - g(b), y - b) - g'(b) < epsilon .
  $

  Taking the first of these inequalities and substituting our choice of $epsilon = g'(b)$, we get
  $
    frac(g(y) - g(b), y - b) > 0
  $

  whenever $y in [a,b]$ and $0 < abs(y-b) < delta_b$. Let $y_b$ be any such $y$. Then, since $y_b < b$, when we multiply by $y_b - b$ the inequality flips and we get
  $
    g(y_b) < g(b) .
  $

  With all that done we can give the main argument for the theorem: since $g$ is differentiable on $[a,b]$, it is continuous on $[a,b]$. By compactness of $[a,b]$, $g$ attains a minimum somewhere on $[a,b]$. The minimum can't be at $a$, since $g(x_a) < g(a)$, and it can't be at $b$ since $g(y_b) < g(b)$. So the minimum must be in $(a,b)$. Call it $c$. Then by the Interior Extremum Theorem, $g'(c) = 0$. So
  $
    f'(c) = alpha .
  $
  
]

= Problem 6: Continuity and differentiability of the inverse
Exercise 5.2.12

=== Proof idea

To show that $f^(-1)$ is continuous when $f$ is continuous on a compact domain, use the preimage-of-closed-sets characterization of continuity. This proof isn't purely topological because it relies on compact sets being closed; it only works when the codomain space has that property. But we've already proved that for $R^n$ so, not a problem for us right now.

To prove that $f^(-1)$ is differentiable, we can't just use the chain rule on the identity $f^(-1)(f(x)) = x$ because that would presuppose that $f^(-1)$ is differentiable.

== Proofs

#theorem[
  Let $K subset.eq R^n$ be a compact set and $f: K -> R^m$ a continuous and injective function. Let $L = f(K)$ be the range of $f$. Then $f^(-1): L -> K$ is continuous.
]
#proof[
  Let $U subset.eq K$ be any closed subset of the domain of $f$, which is the range of $f^(-1)$. Let $V$ be its preimage under $f^(-1)$. By definition, $V = {y in L: f^(-1)(y) in U}$. Since $f$ and $f^(-1)$ are inverses,
  $
    f^(-1)(y) = x "iff" f(x) = y .
  $
  So $f^(-1)(y) in U$ iff there's some $x in U$ such that $f(x) = y$. In other words, $f^(-1)(y) in U <=> y in f(U)$, so $V = f(U)$, the image of $U$ under $f$.

  $U$ is a closed subset of a compact set, so $U$ is compact. $V = f(U)$ is the image of a compact set under a continuous function, so $V$ is compact. $V$ is a compact subset of $R^m$, so $V$ is closed. Since $U$ was an arbitrary closed subset of $K$, we have shown that the preimage under $f^(-1)$ of any closed set is closed. Therefore $f^(-1)$ is continuous.
]

In particular, if $f: [a,b] -> RR$ is continuous and injective then its inverse, defined on the range of $f$, is also continuous.

#theorem[
  Let $f: [a,b] -> RR$ be injective and differentiable on $[a,b]$ with $f'(x) != 0$ for all $x in [a,b]$. Then $f^(-1)$ is differentiable with
  $
    (f^(-1))'(y) = 1/f'(x) "where" y = f(x) .
  $
]
#proof[
  Let $g(x) = f^(-1)(x)$ which is continuous by the previous theorem. Fix $d$ to be some point in $[a,b]$. Since $f$ is differentiable on $[a,b]$, it is differentiable at $d$ and so the limit
  $
    f'(d) = lim_(x->d) frac(f(x) - f(d), x-d)
  $
  exists and is nonzero by the theorem's hypothesis.

  Define
  $
    h(x) = frac(f(x) - f(d), x - d),
  $
  the difference quotient of $f$ at $d$ as a function of $x$. Then $lim_(x->d) h(x) = f'(d)$ exists and is nonzero. Therefore by the Algebraic Limit Theorem for Functional Limits,
  $
    lim_(x->d) 1/h(x) = 1/(f'(d)) .
  $

  By the definition of functional limits, for every $epsilon > 0$ there exists some $delta > 0$ such that $0 < abs(x-d) < delta$ implies that
  $
    abs(1/h(x) - 1/(f'(d))) < epsilon .
  $ <eq2>

  Let $y = f(x)$ for every $x in [a,b]$, and $c = f(d)$ for the fixed point $d$. Then $g(y) = x$ and $g(c) = d$. By continuity of $g$, given this $delta$ there exists some $eta > 0$ such that whenever $0 < abs(y-c) < eta$ we have
  $
    abs(g(y) - g(c)) = abs(x-d) < delta .
  $ <eq3>

  To combine @eq2 and @eq3 we consider $h$ as a function of $y$, which I will write out in detail,
  $
    h(x) = h(g(y)) = frac(f(g(y)) - f(g(d)), g(y) - g(c)),
  $
  to point out that this is justified because $g$ is injective, so $g(y) != g(c)$ whenever $y != c$. We know $g$ must be injective because it has an inverse, namely $f$. And we know $y != c$ when applying @eq3 because $0 < abs(y-c) < eta$. Also note that we need $g(y) != g(c)$, i.e., that $x != d$, because the hypothesis for @eq2 is $0 < abs(x-d) < delta$.
  
  So! By combining @eq2 and @eq3 we see that given $epsilon > 0$ there exists some $eta > 0$ such that whenever $0 < abs(y-c) < eta$ we have
  $
    abs(1/h(x) - 1/(f'(d))) < epsilon .
  $

  In other words,
  $
    lim_(y->c) 1/h(x) = 1/(f'(d)) .
  $

  But this left hand side is
  $
    lim_(y->c) frac(x-d,f(x) - f(d)) = lim_(y->c) frac(g(y) - g(c), y - c) = g'(c) .
  $
]
