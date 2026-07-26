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


= Problem 1: Integrability of $abs(f)$ and the triangle inequality for integration
Exercise 7.4.1

Let $f$ be a bounded function on a set $A$, and set

$
  & M = sup{f(x): x in A}, quad m = inf{f(x): x in A}, \
  & M' = sup{abs(f(x)): x in A}, quad "and" m' = inf{abs(f(x)): x in A}
$

== (a)

#lemma[
  $M - m >= M' - m'$
]
#proof[
  This is inelegant but I will do a case analysis that I'm pretty sure is correct.

  Suppose that $f(x) >= 0$ for all $x in A$. Then $M = M'$ and $m = m'$ and the result follows with both sides of the inequality being equal.

  Otherwise suppose that $f(x) <= 0$ for all $x in A$. Then $M = -m'$ and $m = -M'$ and the result follows with both sides of the inequality being equal.

  Otherwise the function takes values on both sides of zero and we must have $M >= 0$ and $m <= 0$. Then
  $
    M' = max(M, -m) <= M + (-m) = M - m .
  $
  Then, since $m' >= 0$, we have
  $
    M' - m' <= M' <= M - m .
  $
]

== (b)

#lemma[
  If $f$ is integrable on $[a,b]$, then $abs(f)$ is also integrable on this interval.
]
#proof[
  Let $epsilon > 0$ be given. Since $f$ is integrable, there exists some partition $P$ such that
  $
    U(f,P) - L(f,P) < epsilon .
  $
  Write out the sum:
  $
    U(f,P) - L(f,P) = sum_(k=1)^n (M_k - m_k) Delta x_k .
  $

  Let $M'_k$ and $m'_k$ be the corresponding $sup$ and $inf$ of $abs(f)$ over the same subintervals $[x_(k-1), x_k]$. Then, by the previous lemma,
  $
    M'_k - m'_k <= M_k - m_k
  $
  on each subinterval of $P$, so, summing over all subintervals,
  $
    U(abs(f),P) - L(abs(f),P) = sum_(k=1)^n (M'_k - m'_k) Delta x_k <= sum_(k=1)^n (M_k - m_k) Delta x_k = U(f,P) - L(f,P) < epsilon.
  $
  Thus we have exhibited a partition $P$ satisfying the criterion for integrability, so $abs(f)$ is integrable.
]

== (c)
#theorem[
  If $f$ is integrable on $[a,b]$ then $abs(integral_a^b f) <= integral_a^b abs(f)$.
]
#proof[
  By the lemma above, $abs(f)$ is integrable on $[a,b]$, so by Theorem 7.4.2 (ii) with $k=-1$, so is $-abs(f)$. Now, for any $x in [a,b]$ we have
  $
    -abs(f(x)) <= f(x) <= abs(f(x)).
  $
  so, by Theorem 7.4.2 (iv) we have
  $
    integral_a^b -abs(f) <= integral_a^b f <= integral_a^b abs(f) .
  $
  By Theorem 7.4.2 (ii), $integral_a^b -abs(f) = - integral_a^b abs(f)$, so
  $
    -integral_a^b abs(f) <= integral_a^b f <= integral_a^b abs(f)
  $
  which is equivalent to
  $
    abs(integral_a^b f) <= integral_a^b abs(f)
  $
]

= Problem 2: Another episode of our favorite show "Prove or give counterexample"
Exercise 7.4.3

== (a)
It is FALSE that "If $abs(f)$ is integrable on $[a,b]$, then $f$ is also integrable on this set."

Define
$
  f(x) = cases(
    1 quad & "if" x in QQ,
    -1 quad & "if" x in.not QQ .
  )
$

Then $abs(f)$ is the constant function $abs(f(x)) = 1$, which is integrable on any interval. But $f$ is not integrable on $[0,1]$, because $g(x) = (f(x) + 1)/2$ is the Dirichlet function, so if $f$ were to be integrable then so would $g$, which is impossible.

== (b)

It is FALSE that "If $g$ is integrable and $g(x) >= 0$ on $[a,b]$, and $g(x) > 0$ for an infinite number of points $x in [a,b]$, then $integral_a^b > 0$".

Thomae's function is a counterexample. We showed in the last problem set that it's integrable. It is non-negative and takes positive values for all rational numbers. Yet, as we previously showed, its integral over $[0,1]$ is 0.

== (c)

#theorem[
  If $g$ is continuous on $[a,b]$ and $g(x) >= 0$ with $g(y_0) > 0$ for at least one point $y_0 in [a,b]$, then $integral_a^b g > 0$.
]
#proof[
  Set $epsilon = g(y_0) slash 2$ in the definition of continuity to obtain a $delta > 0$ such that $abs(x-y_0) < delta$ implies $g(x) > 0$. Without loss of generality let $delta$ be small enough such that the entire $delta$-neighbourhood of $y_0$ is interior to $[a,b]$. Now break up the interval $[a,b]$ as the union of intervals
  $
    [a,y_0-delta/2], [y_0-delta/2,y_0+delta/2],[y_0+delta/2,b] .
  $
  By Theorem 7.4.1,
  $
    integral_a^b g = integral_(a)^(y_0 - delta/2) g + integral_(y_0-delta/2)^(y_0+delta/2) g + integral_(y_0+delta/2)^b g .
  $
  By Theorem 7.4.2 (iv) and the fact that $g(x) >= 0$ on $[a,b]$, the first and third terms above are non-negative.

  Now, $g(x) > 0$ on $[y_0-delta/2, y_0+delta/2]$ and the function is continuous on this compact set. So it attains its minimum at some point $x_0$ in this subinterval. So $g(x) >= g(x_0) > 0$ and by property (iii) of Theorem 7.4.2, the second term is strictly positive. 
  The argument above relies $y_0 in (a,b)$. If $y_0 = a$ or $y_0 = b$ then the same argument works except that we have two terms instead of three in the decomposition of the interval, one non-negative and one strictly positive.
]

= Problem 3: The integral of a strictly positive function is strictly positive
Exercise 7.4.4

#theorem[
  If $f(x) > 0$ for all $x in [a,b]$ and $f$ is integrable on $[a,b]$ then $integral_a^b f > 0$.
]
#proof[
  I tried many ways of proving it but I couldn't figure it out. Here's an argument that cheats by using a result from the special section later on, which we've discussed in person.

  Since $f$ is integrable, by Lebesgue's Criterion it must be continuous at at least one point $y_0 in [a,b]$. By continuity at $y_0$ there exists a $delta > 0$ such that $f(x) >= f(y_0) slash 2$ for all $x$ in a $delta$-neighborhood of $y_0$. Then, breaking up the interval into three pieces as in the proof for Problem 2 (c), we have
  $
    integral_a^b f = integral_(a)^(y_0 - delta/2) f + integral_(y_0-delta/2)^(y_0+delta/2) f + integral_(y_0+delta/2)^(b) f
  $
  where the first and third terms are non-negative. By Theorem 7.4.2 (iii),
  $
    integral_(y_0-delta/2)^(y_0+delta/2) f >= delta f(y_0)/2 > 0
  $
  and the conclusion follows.
]

= Problem 4: The product of integrable functions is integrable
Exercise 7.4.6

== (a)

Since $abs(f(x)) <= M$ for all $x in [a,b]$, by the triangle inequality we have
$
  abs(f(x) + f(y)) <= abs(f(x)) + abs(f(y)) <= 2M .
$
Then
$
  f(x)^2 - f(y)^2 = (f(x) + f(y))(f(x) -f(y))
$
so
$
  abs(f(x)^2 - f(y)^2) <= 2M abs(f(x) - f(y))
$

== (b)
#lemma[
  If $f$ is integrable on $[a,b]$, then so is $f^2$.
]
#proof[
  Since $f$ is integrable on $[a,b]$ it is bounded on this set. So there exists some $M > 0$ such that $abs(f(x)) <= M$ for all $x in [a,b]$.

  Let $epsilon > 0$ be given. Since $f$ is integrable on $[a,b]$, there exists some partition $P$ such that
  $
    U(f,P) - L(f,P) < epsilon / (2M) .
  $

  Writing out the sum:
  $
    U(f,P) - L(f,P) = sum_(k=1)^n (M_k - m_k) Delta x_k .
  $

  Let $M'_k$ and $m'_k$ denote the $sup$ and $inf$ of $f^2$ over the $k$'th subinterval.

  In each subinterval, by the result in part (a), we have
  $
    abs(f(x)^2 - f(y)^2) <= 2M abs(f(x) - f(y)) <= 2M(M_k - m_k) .
  $

  But, since $sup g - inf g = sup{g(x) - g(y): x,y in A} = sup{abs(g(x) - g(y)): x,y in A}$ for a bounded function $g: A -> R$, by setting $g = f^2$ we have
  $
    M'_k - m'_k <= 2M (M_k - m_k) .
  $

  So
  $
    U(f^2,P) - L(f^2,P) = sum_(k=1)^n (M'_k - m'_k) Delta x_k <= 2M sum_(k=1)^n (M_k - m_k) Delta x_k < 2M (epsilon/(2M)) = epsilon,
  $
  proving that $f^2$ is integrable.
]

== (c)

#theorem[
  If $f$ and $g$ are integrable on $[a,b]$, then $f g$ is integrable on that set as well.
]
#proof[
  Since $f$ and $g$ are integrable on $[a,b]$, so is $f+g$. By the lemma above, so are $f^2$, $g^2$ and $(f+g)^2$. But
  $
    f g = ((f+g)^2 - f^2 - g^2)/2
  $
  so by Theorem 7.4.2 parts (i) and (ii), $f g$ is integrable as well.
]

= Problem 5
Exercise 7.4.9

#theorem[
  Let $g_n$ and $g$ be uniformly bounded on $[0,1]$, meaning that there exists a single $M > 0$ satisfying $abs(g(x)) <= M$ and $abs(g_(n)(x)) <= M$ for all $n in NN$ and $x in [0,1]$. Assume $g_n -> g$ pointwise on $[0,1]$ and uniformly on any set of the form $[0,alpha]$, where $0 < alpha < 1$. If all the functions are integrable, then
  $
    lim_(n->infinity) integral_0^1 g_n = integral_0^1 g .
  $
]
#proof[
  By Theorem 7.4.1, for every $0 < alpha < 1$,
  $
    integral_0^1 g = integral_0^alpha g + integral_alpha^1 g
  $
  and similarly for $g_n$. By Theorem 7.4.2 property (iii), since $-M <= g(x) <= M$, we have
  $
    -M(1-alpha) <= integral_alpha^1 g <= M(1-alpha)
  $
  which is equivalent to
  $
    abs(integral_alpha^1 g) <= M(1-alpha)
  $ <eq1>
  and similarly for $g_n$.

  Let $epsilon > 0$ be given. By the triangle inequality,
  $
    abs(integral_0^1 g_n - integral_0^1 g)
    = & abs(integral_0^alpha g_n + integral_alpha^1 g_n - integral_0^alpha g - integral_alpha^1 g) \
    <= & abs(integral_0^alpha g_n - integral_0^alpha g) + abs(integral_alpha^1 g_n - integral_alpha^1 g) \
    <= & abs(integral_0^alpha g_n - integral_0^alpha g) + abs(integral_alpha^1 g_n) + abs(integral_alpha^1 g)  
  $

  By the @eq1, there exists some $alpha_0 in (0,1)$ with $1-alpha_0 < epsilon slash (4M)$ such that the second and third terms above are each bounded by $epsilon slash 4$, i.e.,
  $
    abs(integral_alpha^1 g_n) <= epsilon/4
  $
  and
  $
    abs(integral_alpha^1 g) <= epsilon/4 .
  $

  Keeping that $alpha_0$ fixed, by uniform convergence of $g_n -> g$ on the set $[0,alpha_0]$, there exists some $N in NN$ such that
  $
    abs(integral_0^(alpha_0)g_n - integral_0^(alpha_0)g) < epsilon/2
  $
  for every $n >= N$.

  Adding the previous inequalities, we have
  $
    abs(integral_0^1 g_n - integral_0^1 g) < epsilon.
  $
  Since $epsilon > 0$ was arbitrary, by the definition of sequence convergence,
  $
    lim_(n->infinity) integral_0^1 g_n = integral_0^1 g .
  $
]


= Problem 6: What breaks if the integral was just defined as the upper sum?
Exercise 7.4.11

Additivity and scaling would no longer hold. The counterexamples must all involve functions that aren't integrable by the usual definition, because for functions that _are_ the properties will of course still hold.

We'll work in the interval $[0,1]$.

== Additivity

Let $f$ be Dirichlet's function. Then $U(f,P) = 1$ for every partition as we've previously proved, so $U(f) = 1$ and by this definition of the integral, $integral_0^1 f = 1$. Let $g(x) = 1-f$. Then $U(g,P) = 1$ on every partition since the rationals are dense in $RR$, so $U(g) = 1$.

This gives us the contradiction: the function $h(x) = f(x) + g(x) = 1$ so its integral is 1, but $integral_0^1 f + integral_0^1 g = 2$.

== Scaling

Let $f$ be Dirichlet's function and let $g(x) = -f(x)$. Then $U(g,P) = 0$ for every partition since the rationals are dense in $RR$. So $U(f)=1$ but $U(-f) = 0$, which violates the scaling property.

== The remaining properties all still hold with this definition of the integral

=== Property (iii)
If
$
  m <= f(x) <= M
$
then, since
$
  L(f,P) <= U(f) <= U(f,P)
$
for every partition $P$, taking $P$ to be the entire interval we have
$
  m(b-a) <= U(f) <= M(b-a) .
$

=== Property (iv)
If
$
  f(x) <= g(x)
$
then
$
  U(f,P) <= U(g,P)
$
for every partition $P$,
so
$
  U(f) <= U(g).
$

=== Property (v)

If $f$ is integrable then $abs(f)$ is bounded so $abs(f)$ is integrable by this new definition.

Now, since
$
  f(x) <= abs(f(x)),
$

by property (iv) we have
$
  U(f) <= U(abs(f)) .
$ <eq2>

Also,
$
  -f(x) <= abs(f(x))
$
so
$
  U(-f) <= U(abs(f)) .
$

But
$
  U(-f) = -L(f)
$
so
$
  -L(f) <= U(abs(f))
$
so
$
  L(f) >= -U(abs(f))
$
and since $U(f) >= L(f)$ always, we have
$
  U(f) >= -U(abs(f)) .
$ <eq3>

Combining @eq2 and @eq3, we have
$
  -U(abs(f)) <= U(f) <= U(abs(f))
$
which is equivalent to
$
  abs(U(f)) <= U(abs(f))
$


