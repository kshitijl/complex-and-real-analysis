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

= Problem 1: Algebraic Limit Theorem for Functional Limits
(Exercise 4.2.1)

Let $f$ and $g$ be functions defined on a domain $A subset.eq RR$, and assume $lim_(x->c) f(x) = L$ and $lim_(x->c) g(x) = M$ for some limit point $c$ of $A$.

== (a)
#theorem[
  $lim_(x->c)[f(x) + g(x)] = L + M$
]
#proof[
  Let $(x_n) subset A$ be any sequence satisfying $x_n != c$ and $(x_n) -> c$.

  By the Sequential Criterion for Functional Limits, the sequences $f(x_n) -> L$ and $g(x_n) -> M$.

  Define the function $h(x) = f(x) + g(x)$. Then the sequence $h(x_n) = f(x_n) + g(x_n)$ for each $n$.

  By the Algebraic Limit Theorem for sequences, $lim h(x_n) = lim f(x_n) + lim g(x_n) = L + M$. Since the sequence $(x_n)$ was arbitrary, this holds for any sequence satisfying the conditions $x_n != c$ and $(x_n) -> c$. So by the Sequential Criterion for Functional Limits again, this time in the other direction,
  $
    lim_(x->c) h(x) = lim_(x->c)[f(x) + g(x)] = L+M .
  $
]

== (b)
#theorem[
  $lim_(x->c)[f(x) + g(x)] = L + M$
]
#proof[
  Let $epsilon > 0$ be given. Then $lim_(x->c) f(x) = L$ guarantees the existence of a $delta_f$ such that $abs(f(x)-L) < epsilon/2$ whenever $0 < abs(x-c) < delta_f$.

  Similarly, since $lim_(x->c) g(x) = M$, there exists a $delta_g > 0$ such that $abs(g(x) - M) < epsilon/2$ whenever $0 < abs(x-c) < delta_g$.

  Define $delta = min(delta_f, delta_g)$. Then, whenever $0 < abs(x-c) < delta$, we have both $abs(f(x) - L) < epsilon/2$ and $abs(g(x) - M) < epsilon/2$.

  By the triangle inequality,
  $
    & abs(f(x) + g(x) - (L+M)) \
    = & abs((f(x) - L) + (g(x) - M)) \
    <= & abs(f(x) - L) + abs(g(x) - M) \
    < & epsilon/2 + epsilon/2 \
    = & epsilon .
  $

  By the definition of functional limits, $lim_(x->c)[f(x) + g(x)] = L + M$.
]

= Problem 2: Thomae's Function
(Exercise 4.2.3)

=== Proof idea

The main idea here is a mental picture: the set of rational numbers with bounded denominator form a grid of a certain coarseness. They can't get finer than a certain amount. So a bounded set has only finitely many such rationals. If you zoom in far enough, there will be no more grid points left; all the remaining rationals must have bigger denominator, so $t(x) < 1/N$. 

== (a)

The following sequences all converge to 1 without using the number 1 as a term in the sequence:
$
  x_n = (n+1)/n \
  y_n = (n-1)/n \
  z_n = sqrt((n+1)/n)
$

== (b)
From elementary number theory we know that $gcd(n+1,n) = gcd(n-1,n) = 1$, so
$
  t(x_n) = t(y_n) = 1/n .
$

In previous problem sets we have shown that the sequence $a_n = 1/n$ converges to 0. So the sequences $t(x_n)$ and $t(y_n)$ both converge to 0.

Now we analyze $t(z_n)$. Long story short, $z_n$ is always irrational so $t(z_n) = 0$ for every $n$, therefore $lim t(z_n) = 0$.

I wanted to write a proof of this. Here goes.

#lemma[
  If $n >= 2$ is not a perfect square, $sqrt(n)$ is irrational.
]
#proof[
  By the Fundamental Theorem of Arithmetic and by collecting even powers of primes,
  $
    n = x^2 y
  $
  where $y > 1$ and $y$ is squarefree. So $sqrt(n) = x sqrt(y)$ and it suffices to show that $sqrt(y)$ is irrational.

  Now
  $
    y = p_1 dot p_2 dot ... dot p_m
  $
  where the $p_i$ are all prime. Suppose for the sake of contradiction that $sqrt(y)$ is rational. Then it has some lowest form rational representation:
  $
    sqrt(y) = a/b .
  $
  Squaring both sides,
  $
    y = a^2/b^2
  $
  so
  $
    a^2 = b^2 y .
  $

  Since $p_1 | y$, it must divide $b^2 y$ and therefore also $p_1 divides a^2$. Since $p_1$ is prime and divides $a^2$, it must actually divide $a$. But then $p_1^2 divides a^2$, so $p_1^2 divides b^2 y$.

  But now, since $y$ is squarefree, it must be that $p_1 divides b$, contradicting that $a/b$ is in least form. Therefore $sqrt(y)$ is irrational.
]

#lemma[
  $z_n$ is always irrational.
]
#proof[
  For $n >= 1$, $n+1$ and $n$ cannot both be perfect squares: if
  $
    a^2 = b^2 + 1
  $
  then
  $
    (a-b)(a+b) = 1
  $
  so either $a-b = a+b = 1$ or $a-b=a+b=-1$, giving $b=0$ either way.

  So, since $gcd(n+1,n) = 1$, we know $(n+1)/n$ is in lowest form. At least one of the numerator and the denominator is not a perfect square, so, by the lemma above, we know that at least one of $sqrt(n+1)$ and $sqrt(n)$ is irrational.
  
  If exactly one of them is irrational then $z_n$ is irrational, since it is the product of a rational number with an irrational.
  
  If both of them are irrational, then $z_n$ is still irrational, for otherwise suppose that
  $
    sqrt((n+1)/n) = p/q
  $
  where $p/q$ is in lowest form. Then
  $
    (n+1)/n = p^2/q^2
  $
  where both the LHS and RHS are in lowest form and positive. So we must have $n+1 = p^2$ and $n = q^2$, contradicting that $n$ and $n+1$ cannot both be perfect squares. So $z_n$ is irrational.
]

== (c)
#theorem[
  $lim_(x->1) t(x) = 0$
]
#proof[
  To prove this we must show that for every ball $B_(epsilon)(0)$ of radius $epsilon$ centered at 0, there exists a ball $B_(delta)(1)$ of radius $delta$ centered at 1 such that for every $x$ != 1 in $B_(delta)(1)$ we have $t(x) in B_(epsilon)(0)$.
  
  Given $epsilon > 0$, let $S$ be the set of points ${x in RR: t(x) >= epsilon}$. Every nonzero member of this set is rational with lowest form representation $m/n$ where $1 <= n <= 1/epsilon$. There are finitely many such $n$. In any bounded interval $(a,b)$ there are finitely many such rational numbers $m/n$, since $m$ must be within the interval $(floor(n a), ceil(n b))$, and there are only finitely many such $m$.

  Therefore, $S inter (0,2)$ has finitely many points. Choose $delta$ to be half the minimum distance between $1$ and another point. If there is no such point, then let $delta = 1$. Then $S inter (1-delta,1+delta)$ has only one point, namely $x=1$. This is the required $delta$: for every point $x in (1-delta,1+delta)$ where $x != 1$, we have $t(x) < epsilon$.
]

= Problem 3: The $epsilon dash.en delta$ game
(Exercise 4.2.5)

== (a)
#theorem[
  $lim_(x->2) (3x + 4) = 10 .$
]
#proof[
  Let $epsilon > 0$ be given. Set $delta = epsilon/3$. Then, whenever
  $
    abs(x-2) < delta = epsilon/3
  $
  we have
  $
    3 abs(x-2) < epsilon
  $
  so
  $
    abs(3x - 6) < epsilon
  $
  which is the required condition, because $3x - 6 = (3x + 4) - 10$.
]

== (b)
#theorem[
  $lim_(x->0) x^3 = 0$
]
#proof[
  Let $epsilon > 0$ be given. Set $delta = root(3, epsilon)$. Then, whenever
  $
    abs(x) < delta
  $
  we have
  $
    abs(x)^3 < delta^3 = epsilon
  $
  since both $abs(x)$ and $delta$ are positive quantities, so we may multiply the inequality with itself.

  Now $abs(x^3) = abs(x)^3$ by multiplicativity of the absolute value function, so
  $
    abs(x^3) < epsilon
  $
  as required.
]

== (c)
#theorem[
  $lim_(x->2) (x^2 + x - 1) = 5$
]
#proof[
  Let $epsilon > 0$ be given. Set $delta = min(1,epsilon/6)$ so that whenever
  $
    abs(x-2) < delta
  $
  we have
  $
    -1 < x-2 < 1
  $
  so
  $
    4 < x + 3 < 6 .
  $

  Since $x+3 > 0$, $abs(x+3) = x+3$. Therefore $abs(x+3) < 6$.

  Then, whenever
  $
    abs(x-2) < delta,
  $
  since $delta <= epsilon/6$, we have
  $
    abs(x-2) < epsilon/6 .
  $

  Since $abs(x+3) < 6$ and both sides of both inequalities are nonnegative, we may multiply them to obtain
  $
    abs(x+3) abs(x-2) < epsilon .
  $

  By multiplicativity of the absolute value function, $abs(x+3) abs(x-2) = abs((x+3)(x-2)) = abs(x^2 + x - 6)$, so
  $
   abs((x^2 + x - 1) - 5) = abs(x^2 + x - 6) < epsilon
  $
  as required.
]

== (d)
#theorem[
  $lim_(x->3) 1/x = 1/3$
]
#proof[
  Let $epsilon > 0$ be given. Set $delta = min(1, 6epsilon)$.

  Since $delta <= 1$, whenever
  $
    abs(x-3) < delta <= 1
  $
  we have
  $
    x > 2 
  $
  so
  $
    1/abs(x) < 1/2 .
  $

  Then, since
  $
    abs(x-3) < delta \
    "and" \
    1/abs(x) < 1/2
  $
  we have
  $
    frac(abs(x-3), abs(x)) < 1/2 dot delta .
  $
  We divide both sides by 3 to get
  $
    frac(abs(x-3), 3 abs(x)) < 1/2 dot delta/3 <= epsilon 
  $
  from which we obtain, rewriting the LHS,
  $
    abs(1/x - 1/3) < epsilon
  $
  as required.
]

= Problem 4: Infinite Limits
(Exercise 4.2.9)

== (a)
#theorem[
  $lim_(x->0) 1/x^2 = infinity$
]
#proof[
  Let $M > 0$ be given. Set $delta = 1/sqrt(M)$ so that whenever
  $
    0 < abs(x - 0) < delta = 1/sqrt(M)
  $
  we have
  $
    abs(x)^2 < 1/M .
  $
  By multiplicativity of the absolute value function, $abs(x)^2 = abs(x^2)$, so
  $
    abs(x^2) < 1/M .
  $
  For real $x$, $x^2 = abs(x^2)$, so
  $
    x^2 < 1/M.
  $
  The quantities on both sides are positive, so
  $
    1/x^2 > M
  $
  as required.
]

== (b)

#definition[
  $lim_(x->infinity) f(x) = L$ means that for all $epsilon > 0$, there exists some $M > 0$ such that whenever $x > M$, we have $abs(f(x) - L) < epsilon$.
]

Using this definition, we have:
#theorem[
  $lim_(x->infinity) 1/x = 0$
]
#proof[
  Let $epsilon > 0$ be given. Take $M = 1/epsilon$. Then, whenever
  $
    x > 1/epsilon ,
  $
  since both sides of the inequality are positive,
  $
    1/x < epsilon
  $
  and so
  $
    abs(1/x - 0) < epsilon 
  $
  as required.
]

== (c)

#definition[
  $lim_(x->infinity) f(x) = infinity$ means that for all $M > 0$ there exists some $N > 0$ such that whenever $x > N$ we have $f(x) > M$.
]

For example:

#theorem[
  $lim_(x->infinity) 2x = infinity$
]
#proof[
  Let $M > 0$ be given. Set $N = M/2$. Then, whenever
  $
    x > N = M/2
  $
  we have
  $
    2x > M
  $
  as required.
]

= Problem 5: Right and Left Limits
(Exercise 4.2.10)

== (a)
#definition[
  Let $f: A -> RR$, and let $a$ be a limit point of $A inter (a,infinity)$. We say that $lim_(x->a^+) f(x) = L$ provided that, for all $epsilon > 0$, there exists a $delta > 0$ such that whenever $a < x < a + delta$ (and $x in A$) it follows that $abs(f(x) - L) < epsilon$.
]

 #definition[
  Let $f: A -> RR$, and let $a$ be a limit point of $A inter (-infinity,a)$. We say that $lim_(x->a^-) f(x) = L$ provided that, for all $epsilon > 0$, there exists a $delta > 0$ such that whenever $a - delta< x < a$ (and $x in A$) it follows that $abs(f(x) - L) < epsilon$.
]

== (b)
#theorem[
  Let $f: A -> RR$ and let $a$ be a limit point of $A$, of $A inter (-infinity,a)$ and of $A inter (a,infinity)$. Then $lim_(x->a) f(x) = L$ iff both the right- and left-hand limits equal $L$.
]
#proof[
  ($=>$)

  Suppose that $lim_(x->a) f(x) = L$ and let $epsilon$ be given. Then there is some $delta$ such that whenever $0 < abs(x-a) < delta$ (and $x in A$) it follows that $abs(f(x) - L) < epsilon$.

  By a standard property of the absolute value function, the inequality involving delta becomes
  $
    -delta < x-a < delta .
  $
  Adding $a$ to both sides, we get
  $
    a - delta < x < a + delta .
  $

  So for any value of $x$ in $(a-delta, a+delta) inter A$ we are guaranteed that $abs(f(x) - L) < epsilon$. So this guarantee holds for values of $x$ in any subset of this interval (intersected with $A$).

  In particular, $I_L = (a-delta, a) inter A$ and $I_R = (a, a+delta) inter A$ are subsets of $(a-delta, a+delta) inter A$. By the hypotheses of the theorem, $a$ is a limit point of $A inter (-infinity, a)$ and $A inter (a, infinity)$. And for the left- and right-hand limits to equal $L$ means for $abs(f(x) - L) < epsilon$ for $x$ in $I_L$ and $I_R$ respectively.

  ($arrow.double.l$)

  Suppose that both the right- and left-hand limits equal $L$, and let $epsilon$ be given. Let $delta_L$ and $delta_R$ be the $delta$ corresponding to epsilon in the definition of the left- and right-hand limits respectively. Let $delta = min(delta_L, delta_R)$.

  Then we have
  $
    abs(f(x) - L) < epsilon .
  $
  whenever $x in A$ and either
  $
    a-delta < x < a
  $
  or
  $
    a < x < a+delta .
  $

  Subtracting $a$ from both inequalities, we get
  $
    -delta < x-a < 0 \
    "or"\
    0 < x-a < delta
  $
  which is equivalent to
  $
    0 < abs(x-a) < delta
  $
  (and $x in A$) as required.
]
