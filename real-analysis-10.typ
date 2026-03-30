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

= Problem 1: Product topology and pointwise convergence

=== Proof idea

This is straight up just unwinding definitions. The main challenge is that the definitions are a little complicated and have several levels of indirection and conditions.

So it was important to sit quietly for fifteen minutes and concentrate very hard, and also to just explicitly write out what is given and what is to be shown in each of the two directions, even if I didn't yet know how to connect the pieces. It turns out that once that's done the proof is trivial.

== Proof

#theorem[
  Let $(f_n)$ be a sequence of functions in $Y^X$ and let $f in Y^X$. Then $(f_n)$ converges to $f$ in the product topology if and only if it converges pointwise.
]
#proof[

  ($=>$)
  
  Let $x_0 in X$ be any point and let $U_0 subset.eq Y$ be an open set containing $f(x_0)$. Let $V_0 subset.eq Y^X$ be the cylinder set
  $
    V_0 = O(x_0; U_0) = {f: X -> Y: f(x_0) in U_0} .
  $
  
  This is a valid cylinder since the number of points involved is 1, a finite number. Therefore $V_0$ is an open set in the product topology. And $f in V_0$ since $f(x_0) in U_0$.
  
  By convergence of $(f_n) -> f$ in the product topology, there exists some $N in NN$ such that $f_n in V_0$ whenever $n >= N$. By the definition of cylinder set, $f_(n)(x_0) in U_0$ whenever $n >= N$. By the definition of sequence convergence, $(f_(n)(x_0)) -> f(x_0)$. Since $x_0 in X$ was arbitrary, by definition of pointwise converge we have $(f_n) -> f$ pointwise.
  
  ($arrow.l.double$)
  
  Suppose that $(f_n) -> f$ pointwise and let $U subset.eq Y^X$ be any open set containing $f$, in the product topology. Then there is some cylinder set $V subset.eq Y^X$ such that $f in V subset.eq U$. That is, there exist points $x_1, x_2, ..., x_n in X$ and open sets $U_1, U_2, ..., U_n subset.eq Y$ such that $f(x_i) in U_i$ for each $i$.
  
  By pointwise convergence of $(f_n)$ to $f$, there exist natural numbers $M_1, M_2, ..., M_n$ such that $f_(m)(x_i) in U_i$ whenever $m >= M_i$, for each $1 <= i <= n$. Let $M = max(M_1, M_2, ..., M_n)$, which is well-defined since $n$ is finite. Then, whenever $m >= M$ we have $f_(m)(x_i) in U_i$ for all $1 <= i <= n$. By the definition of cylinder sets, $f_(m) in V subset.eq U$ whenever $m >= M$, so $(f_n) -> f$ in the product topology.
]
  
= Problem 2: Whether convergence is uniform depends on the domain
Exercise 6.2.3

=== Proof idea

For me, the main takeaway from this exercise is that changing the domain can change whether convergence is uniform or merely pointwise. And of course that if a sequence of continuous functions converges pointwise to something that's not continuous, then the convergence couldn't have been uniform.

== Proofs

For each $n in NN$ and $x in [0, infinity)$, let
$
  g_(n)(x) = x/(1 + x^n) wide "and" wide h_(n)(x) = cases(
    1 & "if" x >= 1 slash n,
    n x quad & "if" 0 <= x < 1 slash n .
  )
$

== (a)

For $x > 1$,
$
  0 <= x/(1+x^n) <= x/x^n = x^(1-n) -> 0,
$
so by the Squeeze Theorem, $g_(n)(x) -> 0$ for $x > 1$.

$g_(n)(1) = 1 slash 2$ identically.

For $0 <= x < 1$, $x^n -> 0$ so $g_(n)(x) -> x/(1+0) = x$ by the Algebraic Limit Theorem. 

Combining these cases,
$
  g_(n)(x) -> cases(
    x & "if" 0 <= x < 1,
    1 slash 2 quad & "if" x = 1,
    0 & "if" x > 1 .
  )
$

For $h_(n)(x)$, note that $h_(n)(0) = 0$ for every $n in NN$. And for every $x > 0$, whenever $n > 1 slash x$ we have $h_(n)(x) = 1$. So by the definition of pointwise convergence,
$
  h_(n)(x) -> cases(
    0 quad & "if" x = 0,
    1 & "if" x > 0 .
  )
$

== (b)

Let $g_(n)(x) -> g(x)$ and $h_(n)(x) -> h(x)$.

$g_(n)(x)$ and $h_(n)(x)$ are continuous for every $n in NN$: the former by the Algebraic Continuity Theorem, the latter because the Left Hand Limit, Right Hand Limit and $h_(n)(x)$ are all 1 at $x = 1 slash n$.

If the convergence were uniform the limit functions in both cases would be continuous, by the Continuous Limit Theorem. But $g$ is discontinuous at 1 and $h$ is discontinuous at $0$. Hence the convergence is not uniform.

== (c)

Let $X = [2, infinity)$. Then $(g_n)$ converges uniformly to $g$ on $X$:

#proof[
  Let $epsilon > 0$ be given. Then pick $N$ such that
  $
    1/(2^(N-1)) < epsilon,
  $
  for example by setting $N = ceil(2 - log epsilon slash log 2)$. Such an $N$ exists by the Archimedean property.

  Then, for any $x >= 2$ and $n >= N$ we have
  $
    x^n >= 2^n >= 2^N .
  $

  Therefore
  $
    0 <= x/(1+x^n) <= x/x^n = 1/x^(n-1) <= 1/2^(n-1) <= 1/2^(N-1) < epsilon .
  $

  Since the limit function is 0 for all $x in X$, this shows that
  $
    abs(g_(n)(x) - g(x)) = abs(g_(n)(x)) < epsilon .
  $

  Since the choice of $N$ was independent of $x$ and works for all $x in X$, the convergence is uniform.
]

Also, $(h_n)$ converges uniformly to $h$ on $X$:

#proof[
  Let $epsilon > 0$ be given. Set $N = 1$. Then for all $x in X$ we have $h_(n)(x) = 1$ and $h(x) = 1$ as well. So $abs(h_(n)(x) - h(x)) = 0 < epsilon$ for all $n >= N$ and all $x in X$.
]

= Problem 3: Cauchy Criterion for Uniform Convergence
Exercise 6.2.5

=== Proof idea

The main, kinda tricky idea here is this: to bound $f_n - f$ we invoke the existence of some $f_k$ that's close enough to $f$. Now we get $f_n - f_k$ and $f_k - f$, both of which are bounded. The somewhat surprising thing is that _even though $k$ can depend on the point $x$_, that doesn't break uniform convergence, because we just need such a $k$ to exist. Its value doesn't actually change which $N$ we pick. Of course I stole this idea from Abbott's proof that every Cauchy sequence converges; there, a similar role is played by a term of the convergent subsequence we get after invoking Bolzano-Weierstrass. But the role in this proof is more subtle and interesting, in my opinion.

== Proof

#theorem[
  A sequence of functions $(f_n)$ defined on a set $A subset.eq RR$ converges uniformly on $A$ if and only if for every $epsilon > 0$ there exists an $N in NN$ such that $abs(f_(n)(x)- f_(m)(x)) < epsilon$ whenever $m,n >= N$ and $x in A$. 
]
#proof[
  ($=>$)

  Suppose $(f_n)$ is a sequence of functions defined on $A subset.eq RR$ that converges uniformly to $f$. Let $epsilon > 0$ be given. Then by the definition of uniform convergence there exists some $N in NN$ such that
  $
    abs(f_(n)(x) - f(x)) < epsilon/2
  $
  whenever $n >= N$. Then by the triangle inequality we have
  $
    abs(f_(n)(x) - f_(m)(x)) = & abs(f_(n)(x) - f(x) + f(x) - f_(m)(x)) \
    <= & abs(f_(n)(x) - f(x)) + abs(f_(m)(x) - f(x)) \
    < & epsilon/2 + epsilon/2 \
    = & epsilon
  $
  whenever $n,m >= N$ as desired.

  ($arrow.l.double$)

  Pick any $x_0 in A$ and consider the sequence of real numbers $(f_(n)(x_0))$. The hypotheses of the theorem mean that we may apply Cauchy's Criterion for sequences to this sequence. So this sequence converges and we may define the function
  $
    f(x) = lim_(n->infinity) f_(n)(x)
  $
  for each $x in A$.

  Let $epsilon > 0$ be given. Choose $N$ such that $abs(f_(n)(x) - f_(m)(x)) < epsilon slash 2$ for each $x in A$ and $n,m >= N$.

  Then for any $x_0 in A$, since the sequence $(f_(n)(x_0)) -> f(x_0)$, there exists some $k >= N$ such that $abs(f_(k)(x_0) - f(x_0)) < epsilon slash 2$.

  (Note that this $k$ may depend on $x_0$. Note also that there may be smaller indices $k' < N$ such that $abs(f_(k')(x_0) - f(x_0)) < epsilon$, but by convergence of $(f_(n)(x_0))$ to $f(x_0)$, any index $k >= max(k', N)$ will then also satisfy $abs(f_(k)(x_0) - f(x_0)) < epsilon$. The important thing is that $N$ doesn't depend on $x_0$, only on $epsilon$. The choice of $k$ is only used to prove that an $N$ that brings all pairs of functions within $epsilon slash 2$ of each other at every point, will also bring any function in the sequence within $epsilon$ of the limit function.)

  Then
  $
    abs(f_(n)(x_0) - f(x_0)) = & abs(f_(n)(x_0) - f_(k)(x_0) + f_(k)(x_0) - f(x_0)) \
    <= & abs(f_(n)(x_0) - f_(k)(x_0)) + abs(f_(k)(x_0) - f(x_0)) \
    < & epsilon/2 + epsilon/2 \
    = & epsilon .
  $

  Since $x_0 in A$ was arbitrary and the choice of $N$ depended only on $epsilon$, we have shown that $f_n -> f$ uniformly on $A$.
]

= Problem 4: $f(x+1 slash n) -> f$ uniformly when $f$ is uniformly continuous
Exercise 6.2.7

#theorem[
  Let $f$ be uniformly continuous on all of $RR$ and define the sequence of functions $(f_n)$ by
  $
    f_(n)(x) = f(x + 1/n) .
  $
  Then $f_n -> f$ uniformly.
]
#proof[
  Let $epsilon > 0$ be given. By uniform continuity of $f$ on all of $RR$, there exists some $delta > 0$ such that
  $
    abs(f(x) - f(y)) < epsilon
  $
  whenever $abs(x-y) < delta$, for all pairs of points $x,y in RR$.

  Set $N = 1 + ceil(1 slash delta)$, so that $N > 1 slash delta$ and therefore
  $
    1/N < delta .
  $
  Then for any $x in RR$ and any $n >= N$ we have
  $
    abs((x+1 slash n) - x) = 1 slash n <= 1 slash N < delta .
  $

  Therefore
  $
    abs(f(x+1 slash n) - f(x)) < epsilon,
  $
  and the choice of $N$ depended on $delta$, which depended only on $epsilon$, not on the point $x$. So the convergence is uniform.
]

If $f$ is not uniformly continuous but merely continuous on all of $RR$ then the convergence of $(f_n)$ to $f$ need not be uniform. Take
$
  f(x) = x^2 .
$

Let $epsilon > 0$ be given and suppose that some $N in NN$ were the adequate response according to the definition of uniform convergence. Then for $x = N epsilon$ we have
$
  abs(f(x+1/N) - f(x)) = abs((2x)/N + 1/N^2) = abs(2 epsilon + 1/N^2) = 2epsilon + 1/N^2 > epsilon ,
$
a contradiction of the condition for uniform convergence.

= Problem 5: Algebraic combinations of uniformly convergent sequences of functions
Exercise 6.2.9

== (a)

#theorem[
  Let $(f_n)$ and $(g_n)$ be uniformly convergent sequences of functions on some set $A$. Then $(f_n + g_n)$ is uniformly convergent.
]
#proof[
  Let $(f_n) -> f$ and $(g_n) -> g$. Let $epsilon > 0$ be given.

  By uniform convergence of $(f_n)$ to $f$, there exists some $N_f in NN$ such that $abs(f_(n)(x) - f(x)) < epsilon slash 2$ for all $x in A$ and all $n >= N_f$. Similarly there exists some $N_g in NN$ such that $abs(g_(m)(x) - g(x)) < epsilon slash 2$ for all $x in A$ and $m >= N_g$.

  Let $N = max(N_f, N_g)$ and let $n >= N$. Then
  $
    & abs((f_(n)(x) + g_(n)(x)) - (f(x) + g(x))) \
    <= & abs(f_(n)(x) - f(x)) + abs(g_(n)(x) - g(x)) \
    < & epsilon/2 + epsilon/2 \
    = epsilon,
  $
  proving that $(f_n + g_n) -> f + g$ uniformly.
]

== (b)

Let
$
  f_(n)(x) = x + 1 slash n
$

and $g_(n)(x) = f_(n)(x)$. So
$
  f_n g_n = (x + 1/n)^2,
$
which is the function discussed in the previous problem. Then since $f(x) = x$ is uniformly continuous, by the previous problem $(f_n) -> f$ and $(g_n) -> f$ uniformly. But, as shown in the previous problem, $(f_n g_n) -> x^2$ but not uniformly.

== (c)

#lemma[
  Let $(f_n)$ be a sequence of functions on some set $A$, converging to $f$. Suppose that there exists some $M > 0$ such that $abs(f_(n)(x)) <= M$ for all $x in A$. Then $abs(f(x)) <= M$ for all $x in A$.
]
#proof[
  Fix some $x_0 in A$. Then the sequence $(f_(n)(x_0))$ is a sequence of real numbers satisfying $-M <= f_(n)(x_0) <= M$. By the definition of pointwise convergence, $(f_(n)(x_0)) -> f(x_0)$. Then by the Order Limit Theorem, $-M <= f(x_0) <= M$. Since $x_0 in A$ was arbitrary, we have $abs(f(x)) <= M$ for all $x in A$.
]

#theorem[
  Let $(f_n)$ and $(g_n)$ be uniformly convergent sequences of functions on some set $A$. Suppose that there exists some $M > 0$ such that $abs(f_n) <= M$ and $abs(g_n) <= M$ for all $n in NN$. Then $(f_n g_n)$ is uniformly convergent.
]
#proof[
  Let $(f_n) -> f$ and $(g_n) -> g$. Then by the lemma above, $abs(f) <= M$.

  Let $epsilon > 0$ be given. By uniform convergence of the two sequences, there exist $N_f, N_g in NN$ such that
  $
    abs(f_(n)(x) - f(x)) < epsilon/(2M) \
    "and" \
    abs(g_(m)(x) - g(x)) < epsilon/(2M)
  $
  whenever $n >= N_f$ and $m >= N_g$. Let $N = max(N_f, N_g)$ and let $n >= N$. We show uniform convergence to the function $f dot g$ by adding and subtracting $f(x) g_(n)(x)$ and applying the triangle inequality:
  $
    & abs(f_(n)(x)g_(n)(x) - f(x)g(x)) \
    = & abs(f_(n)(x)g_(n)(x) - f(x)g_(n)(x) + f(x)g_(n)(x) - f(x)g(x)) \
   <= & abs(f_(n)(x)g_(n)(x) - f(x)g_(n)(x)) + abs(f(x)g_(n)(x) - f(x)g(x)) \
    = & abs(g_(n)(x)) abs(f_(n)(x) - f(x)) + abs(f(x)) abs(g_(n)(x) - g(x)) \
   <= & M dot epsilon/(2M) + M dot epsilon/(2M) \
    = & epsilon .
  $
  
  Since $x in A$ was arbitrary and the choice of $N$ depended only on $epsilon$ and $M$, the convergence is uniform.
]

