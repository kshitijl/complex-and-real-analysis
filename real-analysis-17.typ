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


= Problem 1: Continuous functions whose integral vanishes are identically 0
Exercise 7.5.4

#theorem[
  If $f: [a,b] -> RR$ is continuous and $integral_a^x f = 0$ for all $x in [a,b]$, then $f(x) = 0$ everywhere on $[a,b]$.
]
#proof[
  Since $f$ is continuous, it is integrable on $[a,b]$. Let $F(x) = integral_a^x f$ for $x in [a,b]$. Then by FTC (ii), since $f$ is continuous on $[a,b]$, $F$ is differentiable and $F'(x) = f(x)$ on this interval.

  But $F(x) = 0$ for all $x in [a,b]$ so $F'(x) = 0$ therefore $f(x) = 0$ on this interval.
]

A counterexample when the function is not continuous: let $f: [0,1]$ and
$
  f(x) = cases(
    1 "if" x = 1/2,
    0 "otherwise" .
  )
$

Then $
  integral_0^x f = 0
$

for all $x in [0,1]$ but $f$ is not identically 0.

A more extreme counterexample is Thomae's function. We previously proved that its integral is 0, but it takes nonzero values at a set that's dense in $RR$.

= Problem 2: Differentiable Limit Theorem via FTC
Exercise 7.5.5

#theorem[
  Let $(f_n) -> f$ pointwise and $(f'_n) -> g$ uniformly on $[a,b]$, and suppose that each $f'_n$ is continuous on $[a,b]$. Then $f$ is differentiable and $g(x) = f'(x)$.
]
#proof[
  Since $f'_n$ is continuous, it is integrable and FTC (i) applies:
  $
    integral_a^x f'_n = f_(n)(x) - f_(n)(a)
  $
  so
  $
    f_(n)(x) = f_(n)(a) + integral_a^x f'_n
  $
  for each $x in [a,b]$ and $n in NN$.

  By the Integrable Limit Theorem, since $(f'_n) -> g$ uniformly and each $f'_n$ is integrable (because continuous), $g$ is integrable and
  $
    lim_(n->infinity) integral_a^x f'_(n) = integral_a^x g .
  $
  This holds for all $x in [a,b]$ because uniform convergence on $[a,b]$ implies uniform convergence on any $[a,x]$.

  Combining this with pointwise convergence of $(f_n) -> f$, we have
  $
    f(x) = f(a) + integral_a^x g
  $
  for all $x in [a,b]$.

  Define
  $
    G(x) = integral_a^x g .
  $
  Now $g$ is the uniform limit of continuous functions $f'_n$, so it's continuous on $[a,b]$. So by FTC (ii), $G$ is differentiable on $[a,b]$ and $G'(x) = g(x)$ on that interval. So
  $
    f(x) = f(a) + G(x)
  $
  is also differentiable and $f'(x) = G'(x) = g(x)$.
]

= Problem 3: Integration by Parts
Exercise 7.5.6

== (a)

#theorem[
  Assume $h(x)$ and $k(x)$ have continuous derivatives on $[a,b]$. Then
  $
    integral_a^b h(t) k'(t) dif t = h(b) k(b) - h(a) k(a) - integral_a^b h'(t) k(t) dif t.
  $
]
#proof[
  Define
  $
    f(x) = h(x) k(x). 
  $

  Then, since $h$ and $k$ are differentiable, by the product rule
  $
    f'(x) = h'(x) k(x) + h(x) k'(x) .
  $

  $h$ and $k$ are both continuous since they are differentiable. Since the derivatives are themselves continuous (by hypothesis), by the Algebraic Continuity Theorem, $f'$ is continuous, therefore integrable.

  So we may apply FTC (i) to $f'$ and obtain
  $
    integral_a^b f' = f(b) - f(a),
  $
  i.e.,
  $
    integral_a^b (h'(x) k(x) + h(x) k'(x)) = h(b) k(b) - h(a) k(a) .
  $
  By linearity (since $h'(x) k(x)$ and $h(x) k'(x)$ are continuous, therefore integrable), and since $x$ is just a dummy variable,
  $
    integral_a^b h(t) k'(t) dif t + integral_a^b h'(t) k(t) = h(b) k(b) - h(a) k(a)
  $
  which is equivalent to the desired conclusion.
]

== (b)

We can weaken the hypotheses to: let $h$ and $k$ be differentiable, with integrable derivatives.

Then $h'(x) k(x)$ and $h(x) k'(x)$ are integrable since they are the products of integrable functions, and so is $f'$. The rest of the proof is the same.

= Problem 4: Natural Logarithm and Euler's Constant
Exercise 7.5.8

== (a)

By Definition 7.4.3,
$
  L(1) = integral_1^1 1/t = 0 .
$

The function $1 slash t$ is continuous for all $t in (0,infinity)$.

For $x >= 1$, FTC (ii) applies, the integrand is continuous, so $L$ is differentiable with derivative $L'(x) = 1 slash x$.

Fix $0 < x < 1$, by Definition 7.4.3,
$
  L(x) = integral_1^x 1 slash t = -integral_x^1 1 slash t .
$

Pick any $0 < a < x$. Then by Theorem 7.4.1,
$
  integral_a^1 1 slash t - integral_a^x 1 slash t = integral_x^1 1 slash t .
$

The first term on the LHS is a constant; and FTC (ii) applies directly to the second term, showing that the second term (including its leading minus sign) is a differentiable function with derivative $-1 slash x$. Therefore the RHS is differentiable with derivative $-1 slash x$, so
$
  L(x) = -integral_x^1 1 slash t
$
is differentiable and its derivative is $1 slash x$. Since $x$ was arbitary, this holds for any $0 < x < 1$. Combined with the first part, we see that $L(x)$ is differentiable for $x > 0$ and its derivative is $1 slash x$.

== (b)

Fix $y in (0, infinity)$ and define
$
  g(x) = L(x y) .
$

Then by the Chain Rule,
$
  g'(x) = 1/(x y) dot y = 1 slash x = L'(x).
$

By the Mean Value Theorem, $g$ and $L$ must differ by a constant (as a function of $x$):
$
  g(x) = L(x) + K .
$

Setting $x = 1$, we see that
$
  L(1 dot y) = L(1) + K
$
and since $L(1) = 0$ we have
$
  K = L(y),
$
showing that
$
  L(x y) = L(x) + L(y) .
$

== (c)

From part (b),
$
  0 = L(1) = L(x dot 1/x) = L(x) + L(1/x)
$
so
$
  L(1/x) = -L(x)
$

for all $x > 0$.

Applying part (b) again to $x dot 1 slash y$ (since $1 slash y > 0$),
$
  L(x dot 1/y) = L(x) + L(1/y) = L(x) - L(y) .
$

== (d)

#theorem[
  Let
  $
    gamma_n = (1 + 1/2 + 1/3 + ... + 1/n) - L(n) .
  $
  Then $(gamma_n)$ converges.
]
#proof[
  We will use the Monotone Convergence Theorem. First monotonicity:
  $
    gamma_(n+1) - gamma_n = 1/(n+1) - L(n+1) + L(n) = 1/(n+1) - integral_n^(n+1) 1 slash t dif t
  $
  where the last step follows from Theorem 7.4.1.

  On this interval,
  $
    1/(n+1) <= 1/t
  $
  so by Theorem 7.4.2 (iii) we have
  $
    1/(n+1) dot (n+1 - n) <= integral_n^(n+1) 1 slash t dif t
  $
  so
  $
    1/(n+1) - integral_n^(n+1) 1 slash t dif t <= 0,
  $
  i.e., the sequence is monotonically decreasing.

  Now we must show a lower bound: let $f(x) = 1 slash x$ and let $P$ be the partition ${1,2,3,...,n}$. Then on any subinterval $[k,k+1]$, we have $sup {f(x): x in [k,k+1]} = 1 slash k$. So the upper sum
  $
    U(f,P) = sum_(k=1)^(n-1) 1/k dot 1 = 1 + 1/2 + 1/3 + ... + 1/(n-1) .
  $

  Now, $U(f,P) >= U(f) = integral_1^n 1 slash t dif t = L(n)$, so
  $
    U(f,P) + 1/n >= L(n) + 1/n
  $
  (we write this because the harmonic sum we have is $U(f,P) + 1 slash n$)
  so
  $
    gamma_n = U(f,P) + 1/n - L(n) >= 1/n > 0 .
  $

  By MCT, $(gamma_n)$ converges.
]

== (e)

Let
$
  H_n = 1 + 1/2 + 1/3 + ... + 1/n .
$

Then
$
  gamma_(2n) - gamma_n = H_(2n) - H_n - L(2n) + L(n) .
$

By part (b), $L(2n) = L(2) + L(n)$, so
$
  gamma_(2n) - gamma_n = H_(2n) - H_n - L(2) .
$

Now, $(gamma_(2n))$ is a subsequence of $(gamma_n)$ and therefore converges to the same limit $gamma$. By the Algebraic Limit Theorem, $(gamma_(2n) - gamma_n) -> 0$, so
$
  H_(2n) - H_n -> L(2) .
$

Now,
$
  H_(2n) = & 1 + 1/2 + 1/3 + 1/4 + ... + 1/(2n) \
         = & 1 + 1/3 + 1/5 + ... + 1/(2n-1) + 1/2 (1 + 1/2 + ... + 1/n) \
         = & 1 + 1/3 + 1/5 + ... + 1/(2n-1) + 1/2 H_n
$
so
$
  H_(2n) - H_n = & 1 + 1/3 + 1/5 + ... + 1/(2n-1) + 1/2 H_n - H_n \
               = & 1 + 1/3 + 1/5 + ... + 1/(2n-1) - 1/2 H_n \
               = & 1 - 1/2 + 1/3 - 1/4 + 1/5 - ... - 1/(2n) \
               = & S_(2n)
$
where $S_n$ denotes the alternating harmonic sum with $n$ terms.

Therefore we have shown that $(S_(2n)) -> L(2)$. But as we've shown in previous problem sets, $S_n$ converges by the alternating series test. Since $(S_(2n))$ is a subsequence, they must both converge to the same limit, so $(S_n) -> L(2)$.

= Problem 5: Total Variation
Exercise 7.5.9

Given a function $f$ on $[a,b]$, define the total variation of $f$ to be
$
  V f = sup {sum_(k=1)^n abs(f(x_k) - f(x_(k-1)))}
$

where the $sup$ is taken over all partitions $P$ of $[a,b]$.

Let $V(f,P)$ denote $sum_(k=1)^n abs(f(x_k) - f(x_(k-1)))$ for a given partition $P$.

== (a)

#theorem[
  If $f$ is continuously differentiable, then
  $
    V f <= integral_a^b abs(f') .
  $
]
#proof[
  $f'$ is continuous, therefore integrable.
  
  Let $P$ be some partition of $[a,b]$. Then on any subinterval $[x_(k-1), x_k]$, by FTC (i),
  $
    integral_(x_(k-1))^(x_k) f' = f(x_k) - f(x_(k-1)) .
  $

  Taking the absolute value on both sides and summing over all subintervals,
  $
    V(f,P) = sum_(k=1)^n abs(f(x_k) - f(x_(k-1))) = sum_(k=1)^n abs(integral_(x_(k-1))^(x_k) f') .
  $

  By the triangle inequality for integrals Theorem 7.4.2 (v), $abs(f')$ is integrable and
  $
    V(f,P) = & sum_(k=1)^n abs(integral_(x_(k-1))^(x_k) f') \
    <= & sum_(k=1)^n integral_(x_(k-1))^(x_k) abs(f') \
    =  & integral_a^b abs(f')
  $
  where the last step follows from Theorem 7.4.1. We have shown that $integral_a^b abs(f')$ is an upper bound for $V(f,P)$ for any partition $P$, while $V f$ is the _least_ upper bound for the set of all $V(f,P)$, so
  $
    V f <= integral_a^b abs(f') .
  $
]

== (b)

#theorem[
  If $f$ is continuously differentiable on $[a,b]$ then
  $
    integral_a^b abs(f') <= V f .
  $
]
#proof[
  Let $P$ be some partition of $[a,b]$. Then since $f$ is differentiable on every subinterval, we may apply MVT to obtain
  $
    f(x_k) - f(x_(k-1)) = f'(c_k) (x_k - x_(k-1))
  $
  for some $c_k in (x_(k-1), x_k))$. Taking absolute values and summing over all subintervals, we obtain
  $
    V(f,P) = sum_(k=1)^n abs(f(x_k) - f(x_(k-1))) = sum_(k=1)^n abs(f'(c_k)) (x_k - x_(k-1)) .
  $

  The quantity on the RHS is $>=$ the lower sum $L(abs(f'),P)$ because $abs(f'(c_k)) >= inf{abs(f'(x)): x in [x_(k-1), x_k]}$.

  Now,
  $
    V f >= V(f,P)
  $
  for every $P$ since $V f$ is the supremum of $V(f,P)$ over all partitions, so
  $
    V f >= V(f,P) >= L(abs(f'), P)
  $
  for every $P$. In other words, $V f$ is an upper bound for the lower sums $L(abs(f'), P)$, so it is $>=$ the _least_ upper bound $L(abs(f'))$, which is equal to $integral_a^b abs(f')$ since $abs(f')$ is integrable.
]

= Problem 6: Change-of-variable formula
Exercise 7.5.10

Let $g: [a,b] -> RR$ be differentiable and assume $g'$ is continuous. Let $f: [c,d] -> RR$ be continuous, and assume that the range of $g$ is contained in $[c,d]$ so that the composition $f compose g$ is properly defined.

#lemma[
  Any continuous function on a closed interval has an antiderivative.
]
#proof[
  Let $h: [alpha, beta] -> RR$ be continuous, therefore integrable. Define
  $
    H(x) = integral_alpha^x h .
  $
  Then by FTC (ii), since $h$ is continuous, $H$ is differentiable at every $x in [alpha,beta]$ and $H'(x) = h(x)$. We have exhibited the required antiderivative.
]

== (a)

By the lemma above, since $f$ is continuous, it is the derivative of a function. Also, $f compose g$ is continuous by Theorem 4.3.9, and $g'$ is continuous by hypothesis, so $(f compose g) g'$ is continuous by the Algebraic Continuity Theorem. So, by the lemma above, $(f compose g) g'$ is the derivative of some function.

== (b)

#theorem[
  Under the hypotheses above on $f$ and $g$,
  $
    integral_a^b f(g(x)) g'(x) dif x = integral_(g(a))^(g(b)) f(t) dif t
  $
]
#proof[
  By the lemma above, $f$ has an antiderivative. Call it $F$ and consider
  $
    H(x) = F(g(x)) .
  $
  By the chain rule, since $F'(x) = f(x)$ on $[c,d]$, its derivative is
  $
    H'(x) = f(g(x)) g'(x)
  $
  which is continuous, therefore integrable on $[a,b]$. By FTC (i),
  $
    integral_a^b f(g(x)) g'(x) dif x = H(b) - H(a) = F(g(b)) - F(g(a)).
  $

  Suppose $g(b) >= g(a)$. Then by FTC (i) applied to $f$ on $[g(a), g(b)]$ we get
  $
    integral_(g(a))^(g(b)) f(t) dif t = F(g(b)) - F(g(a)) .
  $
  Otherwise, $g(a) > g(b)$ and we apply FTC (i) to $f$ on $[g(b), g(a)]$ and apply the convention from Definition 7.4.3 to get
  $
    integral_(g(a))^(g(b)) f(t) dif t = -integral_(g(b))^(g(a)) f(t) dif t = -(F(g(a)) - F(g(b))) = F(g(b)) - F(g(a)) .
  $

  Either way,
  $
    integral_(g(a))^(g(b)) f(t) dif t = F(g(b)) - F(g(a)) = integral_a^b f(g(x)) g'(x) dif x .
  $

]

