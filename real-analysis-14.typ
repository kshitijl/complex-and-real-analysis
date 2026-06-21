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

= Problem 0: Combinatorial proof that $sum_(k=0)^n (-1)^k binom(n,k) = 0$

#theorem[
  Let $S$ be a set with $n$ elements where $n > =1$. Then the number of even-sized subsets of $S$ is the same as the number of odd-sized subsets of $S$.
]
#proof[
  I previously proposed "flipping all bits", i.e., mapping every subset to its complement. This works for odd $n$: it bijectively maps odd-sized subsets to even-sized subsets and vice-versa, hence proving that the number of each is equal. But for even $n$ the map doesn't change the parity.

  Instead, let's pick some element, say $a in S$. This is possible because $n>=1$. Let $T subset.eq S$ be any subset. Then define the map $f: 2^S -> 2^S$ as follows:
  $
    f(T) = cases(
      T union {a} "if" a in.not T,
      T backslash {a} "if" a in T .
    )
  $

  In other words, we toggle the presence of this element $a$, or "flip the first bit".

  This is a bijection because it is its own inverse: applying this map twice gives the original subset back.

  It always changes the parity of a subset because it always changes the number of elements by 1: for subsets that contain $a$ it removes one, and for subsets that don't it adds one.

  Thus we have exhibited a bijection between odd-sized and even-sized subsets. So there are an equal number of each.
]

= Problem 1: Cauchy's Remainder Theorem
Exercise 6.6.9

Let $f$ be differentiable $N+1$ times on $(-R,R)$. For each $a in (-R,R)$, let $S_(N)(x,a)$ be the partial sum of the Taylor series for $f$ centered at $a$; in other words, define
$
  S_(N)(x,a) = sum_(n=0)^N c_n (x-a)^n
$
where
$
  c_n = frac(f^(n)(a), n!).
$

Let
$
  E_(N)(x,a) = f(x) - S_(N)(x,a) .
$

Fix $x != 0$ in $(-R,R)$.

== (a)

We first note that when $a=x$ the factor
$
  c_0 = f(x)/0! = f(x) .
$

Now substituting $a=x$ in the expression for $E_N$,
$
  E_(N)(x,x) = f(x) - S_(N)(x,x) = f(x) - sum_(n=0)^N c_n (x-x)^n = f(x) - c_0 = 0,
$
where all terms in the sum $S_(N)(x,x)$ are zero except $n=0$.

== (b)

$S_(N)(x,a)$ as a function of $a$ is a finite sum of terms, each of which is the product of a polynomial $(x-a)^n$ and $f^(n)(a)/n!$ where $n <= N$. By hypothesis, $f$ is differentiable $N+1$ times, so each factor in the product is differentiable at least once. By the product and sum rules for differentiation, the entire finite sum is differentiable.

$E_(N)(x,a) = f(x) - S_(N)(x,a)$, but $f(x)$ is a constant with respect to $a$. So $E_(N)(x,a)$ is differentiable with respect to $a$ simply because $S_(N)(x,a)$ is differentiable with respect to $a$.

For $n>=1$ the term with index $n$ in the finite sum $S_N$ is
$
  frac(f^(n)(a) (x-a)^n, n!)
$
so its derivative, using the ordinary rules of differentiation, is
$
  frac(f^(n+1)(a) (x-a)^n, n!) - frac(f^(n)(a) (x-a)^(n-1), (n-1)!) .
$

For $n=0$ the term is simply $f(a)$ and its derivative is $f'(a)$.

Summing over all $n$ we find that consecutive positive and negative terms cancel, leaving
$
  S'_(N)(x,a) = (f^(N+1)(a))/N! (x-a)^N .
$

So
$
  E'_(N)(x,a) = frac(-f^(N+1)(a),N!) (x-a)^N .
$

== (c)

Let $g(a) = E_(N)(x,a)$. Then $g$ is differentiable on $(-R,R)$ and therefore also continuous on that interval. So it satisfies the hypotheses for the Mean Value Theorem for any closed interval contained in $(-R,R)$.

For $x > 0$ we apply the Mean Value Theorem to $g(a)$ on the interval $[0,x]$:
$
  frac(g(x) - g(0), x- 0) = g'(c)
$
for some $c in (0,x)$.

This evaluates to
$
  g(x) - g(0) = x g'(c) = - x frac(f^(N+1)(c),N!) (x-c)^N .
$

But $g(x) = 0$ and $g(0) = E_(N)(x,0)$ so
$
  E_(N)(x,0) = x frac(f^(N+1)(c),N!) (x-c)^N
$
as desired.

When $x < 0$ an exactly analogous application of MVT to the interval $[x,0]$ produces the same result.

= Problem 2: Convergence of Taylor series for $1 slash sqrt(1-x)$
Exercise 6.6.10

I suspect I have greatly overcomplicated this one, but I think it works. I found some identities on Wikipedia for the double factorial that I used here, and the log identity comes from the Taylor series for log from calculus that we haven't shown in this book. There must be a simpler way...

I'll use the double factorial notation
$
  n!! = n dot (n-2) dot (n-4) dots.c 1
$
for odd $n$ and
$
  n!! = n dot (n-2) dot (n-4) dots.c 2
$
for even $n$.

Then the $n$'th derivative of $f(x) = 1 slash sqrt(1-x)$ is
$
  f^(n)(x) = (2n-1)!!/2^n (1-x)^(-(2n+1)/2) .
$

Evaluating at $x=0$ gives the Taylor series
$
  1 + sum_(n=1)^infinity (2n-1)!!/(2^n n!) x^n
$

== (a)

The function is infinitely differentiable on $(-1,1)$ so Lagrange's Remainder Theorem applies. The error term from Lagrange's Remainder Theorem is
$
  E_(N)(x) = (f^(N+1)(c))/(N+1)! x^(N+1)
$
for some $abs(c) < abs(x)$. This evaluates to
$
  E_(N)(x) = (2N+1)!!/(2^(N+1) (N+1)!) (1-c)^(-(2N+3)/2) x^(N+1) .
$

For $x in [0,1/2]$,
$
  abs(x) <= abs(1/2)
$
so
$
  abs(x^(N+1)) <= 1/2^(N+1) .
$

Also, $abs(c) < abs(x)$ by the Theorem so $0 <= c < x <= 1/2$ so
$
  1-c > 1/2 
$
so
$
  (1-c)^(-(2N+3)/2) < 2^((2N+3)/2) .
$

Therefore

$
  abs(E_(N)(x)) < (2N+1)!!/(2^(N+1) (N+1)!) 2^((2N+3)/2) 1/2^(N+1) = (2N+1)!!/((N+1)! 2^((2N+1)/2)) .
$

Write the power-of-two factor in the denominator as
$
  2^((2N+1)/2) = 2^(N+1)/sqrt(2)
$
so we can multiply $2^(N+1)$ with the factorial.

Writing out the factorial and multiplying every term by 2 gives
$
  2^(N+1) (N+1)! = 2^(N+1) (N+1) dot N dot (N-1) dots.c 1 = (2N+2) dot 2N dot (2N-2) dots.c 2 = (2N+2)!!
$
so the error term bound becomes
$
  abs(E_(N)(x)) < sqrt(2) frac((2N+1)!!, (2N+2)!!) .
$

Writing out the double factorial ratio explicitly,
$
  (2N+1)!!/(2N+2)!! = 1/2 dot 3/4 dot 5/6 dots.c (2N+1)/(2N+2) = product_(k=1)^(N+1) (2k-1)/(2k) = product_(k=1)^(N+1) (1 - 1/(2k)) .
$

Taking logarithms and using the fact that $log(1-t) <= -t$ for $t in [0,1)$,
$
  log abs(E_(N)(x)) <= (log 2)/2 - sum_(k=1)^(N+1) 1/(2k) .
$

The sum on the RHS is $-1/2$ times the harmonic sum and therefore diverges to $-infinity$, so $E_(N)(x) -> 0$.

For $x>1/2$, the bound we can get from the Lagrange Remainder blows up: in the worst case $1-c -> 1-x$ which gives
$
  E_(N)(x) ~ "all the double factorial stuff" dot (x/(1-x))^(N+1) dot 1/sqrt(1-x)
$
which blows up geometrically for $x>1/2$ while the double factorial stuff only decays as $sqrt(N)$.

== (b)

Cauchy's Remainder Theorem gives
$
  E_(N)(x) = (f^(N+1)(c))/N! (x-c)^N x
$
for some $c$ between 0 and $x$. This evaluates to
$
  (2N+1)!!/(2^(N+1) N!) (1-c)^(-(2N+3)/2)(x-c)^N x  = (2N+1)!!/(2^(N+1) N!) dot ((x-c)/(1-c))^N dot (1-c)^(-3/2) dot x .
$

For $x=0$ convergence is trivial. So we assume $x != 0$.

For $x in (0,1)$ we have
$
  0 < x < 1
$
and
$
  0 < c < x .
$

Write
$
  (x-c)/(1-c)
$
as
$
  (1-c - (1-x))/(1-c) = 1 - (1-x)/(1-c) .
$

As $c$ grows, $1-c$ becomes smaller, so $1/(1-c)$ gets bigger, so $-1/(1-c)$ gets smaller. So
$
  (x-c)/(1-c)
$
has its maximum at $c=0$, i.e.,
$
  (x-c)/(1-c) <= x
$
so
$
  ((x-c)/(1-c))^N <= x^N .
$

Now,
$
  0 < c < x
$
so
$
  1 > 1-c > 1-x
$
so
$
  1 < (1-c)^(-3/2) < (1-x)^(-3/2) .
$

Putting these bounds together we have
$
  abs(E_(N)(x)) <= (2N+1)!!/(2^(N+1)N!) dot x^N dot (1-x)^(-3/2) dot x
$

Similar to the previous part, we write
$
  2^(N+1) N! = (2N+2)!!/(N+1)
$
so
$
  (2N+1)!!/(2^(N+1)N!) = frac((2N+1)!! (N+1), (2N+2)!!) <= N+1,
$
so the whole error is bounded by
$
  abs(E_(N)(x)) <= (N+1) x^(N+1) (1-x)^(-3/2) .
$

This goes to 0 by the Ratio Test for sequences because the ratio of consecutive terms is
$
  x (N+2)/(N+1) -> x < 1 .
$

Phew!

= Problem 3: $U(f) >= L(f)$
Exercise 7.2.1

#lemma[
  Let $f$ be a bounded function on $[a,b]$ and let $P$ be an arbitrary partition of $[a,b]$. Then $U(f) >= L(f,P)$.
]
#proof[
  Let $cal(P)$ be the set of all possible partitions of the interval $[a,b]$. Then by Lemma 7.2.4, for any partition $Q in cal(P)$,
  $
    L(f,P) <= U(f, Q).
  $
  In other words, $L(f,P)$ is a lower bound for the set of all upper sums ${U(f,Q): Q in cal(P)}$. But $U(f)$ is defined to be the _greatest_ lower bound of the set of all upper sums, so $U(f) >= L(f,P)$.
]

#lemma[
  For any bounded function $f$ on $[a,b]$, it is always the case that $U(f) >= L(f)$.
]
#proof[
  Since the partition $P$ in the previous lemma was arbitrary, $U(f)$ is an upper bound of the set of all lower sums ${L(f,P): P in cal(P)}$. But $L(f)$ is defined as the _least_ upper bound of this set, so $L(f) <= U(f)$.
]

= Problem 4: Sequential Criterion for Integrability
Exercise 7.2.3

== (a)

#theorem[
  A bounded function $f$ is integrable on $[a,b]$ if and only if there exists a sequence of partitions $(P_n)^(infinity)_(n=1)$ satisfying
  $
    lim_(n->infinity) [U(f,P_n) - L(f,P_n)] = 0,
  $
  and in this case
  $
    integral_a^b f = lim_(n->infinity) U(f,P_n) = lim_(n->infinity) L(f,P_n) .
  $
]
#proof[

  ($=>$)

  Suppose $f$ is integrable on $[a,b]$. Then by putting $epsilon = 1 slash n$ for every $n$ in Theorem 7.2.8 (Integrability Criterion), we obtain a sequence of partitions $P_n$ of $[a,b]$ such that
  $
    U(f,P_n) - L(f,P_n) < 1 slash n.
  $

  Also
  $
    U(f,P_n) >= L(f,P_n)
  $
  since on every subinterval of the partition, the supremum of the function is greater than or equal to the infimum.

  So
  $
    0 <= U(f,P_n) - L(f,P_n) < 1 slash n
  $
  
  so by the Squeeze Theorem,
  $
    lim_(n->infinity) [U(f,P_n) - L(f,P_n)] = 0 .
  $

  ($arrow.double.l$)

  Suppose that there is a sequence of partitions satisfying
  $
    lim_(n->infinity) [U(f,P_n) - L(f,P_n)] = 0 .
  $

  Let $epsilon>0$ be given. Then by the definition of limit, there exists some $N in NN$ such that
  $
    abs(U(f,P_n) - L(f,P_n)) < epsilon
  $
  whenever $n >= N$. Therefore
  $
    U(f,P_N) - L(f,P_N) < epsilon
  $
  so by the Integrability Criterion in the other direction, since $epsilon$ was arbitrary, $f$ is integrable on $[a,b]$.

  Now since the function is integrable, $U(f) = L(f)$. Since $L(f)$ is the supremum of all lower sums and $U(f)$ the infimum of all upper sums,
  $
    L(f,P_n) <= L(f) = U(f) <= U(f,P_n)
  $
  so
  $
    0 <= I - L(f,P_n) <= U(f,P_n) - L(f,P_n)
  $
  and
  $
    0 <= U(f,P_n) - I <= U(f,P_n) - L(f,P_n) 
  $

  where $I = U(f) = L(f)$ is the integral.

  By the Squeeze Theorem applied to both these inequalities,
  $
    lim_(n->infinity) U(f,P_n) = lim_(n->infinity) L(f,P_n) = I .
  $
]

== (b)

For each $n$ let $P_n$ be the partition of $[0,1]$ into $n$ equal subintervals and $f(x) = x$. Then the supremum of $f$ on the $k$'th subinterval is $k slash n$ and the infimum is $(k-1) slash n$ for $k = 1 .. n$. And each subinterval has length $1 slash n$. So
$
  U(f,P_n) = 1/n [1/n + 2/n + ... + (n-1)/n + n/n] = 1/n dot 1/n dot n(n+1)/2 = (n+1)/(2n)
$
and
$
  L(f,P_n) = 1/n [0/n + 1/n + ... + (n-1)/n] = 1/n dot 1/n dot n(n-1)/2 = (n-1)/(2n) .
$

== (c)

$
  U(f,P_n) - L(f,P_n) = 1/n
$
whose limit is 0 as $n->infinity$, so by the criterion in part (a), $f(x) = x$ is integrable on $[0,1]$. Taking the limit of $U(f,P_n)$,
$
  integral_0^1 f = lim_(n->infinity) (n+1)/(2n) = 1/2 .
$

= Problem 5: The uniform limit of integrable functions is integrable
Exercise 7.2.5

The main idea is to bound the difference $M^f_k - m^f_k$ in terms of $M^(f_n)_k - m^(f_n)_k$, then use the Integrability Criterion in both directions.

#theorem[
  Suppose that for each $n$, $f_n$ is an integrable function on $[a,b]$. If $(f_n) -> f$ uniformly on $[a,b]$ then $f$ is also integrable on this set.
]
#proof[
  If $a=b$ then the conclusion is trivial, so we assume $b > a$.
  
  Let $epsilon > 0$ be given and let
  $
    delta = epsilon / (4 (b-a)) .
  $

  By uniform convergence of $(f_n)$ to $f$, there exists some $N in NN$ such that whenever $m >= N$, for any point $x in [a,b]$ we have

  $
    abs(f(x) - f_(m)(x)) < delta.
  $
  This is equivalent to the following inequalities which we will use below:
  $
    f(x) < f_(m)(x) + delta
  $
  and
  $
    f_(m)(x) < f(x) + delta.
  $

  Fix any $m >= N$.

  By integrability of $f_m$, there exists some partition $P$ of $[a,b]$ such that
  $
    U(f_m,P) - L(f_m,P) < epsilon/2 .
  $

  Let $[x_(k-1), x_k]$ be the $k$'th subinterval of $P$ and let
  $
    m^(g)_k = inf{g(x): x in [x_(k-1), x_k]}
  $
  and
  $
    M^(g)_k = sup{g(x): x in [x_(k-1), x_k]}
  $
  where $g$ could be $f$ or one of the functions $f_n$.

  Then for any $x in [x_(k-1), x_k]$,
  $
    f(x) < f_(m)(x) + delta <= M^(f_m)_k + delta
  $
  so $M^(f_m)_k + delta$ is an upper bound for the set ${f(x): x in [x_(k-1), x_k]}$. But $M^(f)_k$ is the _least_ upper bound of this set so
  $
    M^(f)_k <= M^(f_m)_k + delta.
  $

  Similarly,
  $
    f_(m)(x) < f(x) + delta <= M^(f)_k + delta
  $
  so $M^(f)_k + delta$ is an upper bound for the set ${f_(m)(x): x in [x_(k-1), x_k]}$, so
  $
    M^(f_m)_k <= M^(f)_k + delta.
  $

  Together, these inequalities are equivalent to
  $
    abs(M^(f)_k - M^(f_m)_k) <= delta.
  $

  By a completely analogous argument,
  $
    abs(m^(f)_k - m^(f_m)_k) <= delta.
  $

  By the triangle inequality,
  $
    M^(f)_k - m^(f)_k =  & abs(M^(f)_k - m^(f)_k) \
    & = abs(M^(f)_k - M^(f_m)_k + M^(f_m)_k - m^(f_m)_k + m^(f_m)_k - m^(f)_k) \
    & <= abs(M^(f)_k - M^(f_m)_k) + abs(M^(f_m)_k - m^(f_m)_k) + abs(m^(f_m)_k - m^(f)_k) \
    & <= abs(M^(f_m)_k - m^(f_m)_k) + 2 delta \
    & <= M^(f_m)_k - m^(f_m)_k + 2 delta.
  $

  Let $P$ have $p$ subintervals. Summing over all $k$, we have
  $
    U(f,P) - L(f,P) = & sum_(k=1)^p (M^(f)_k - m^(f)_k) Delta x_k \
    <= & sum_(k=1)^p (M^(f_m)_k - m^(f_m)_k + 2 delta) Delta x_k \
     = & sum_(k=1)^p (M^(f_m)_k - m^(f_m)_k) Delta x_k + sum_(k=1)^p 2 delta Delta x_k \
     = & U(f_m, P) - L(f_m, P) + 2 delta (b-a) \
     < & epsilon/2 + 2 delta (b-a) \
     = & epsilon/2 + epsilon/2 \
     = & epsilon .
  $

  Since $epsilon > 0$ was arbitrary, by Theorem 7.2.8 (Integrability Criterion), $f$ is integrable.
]

= Problem 6: Increasing functions are integrable
Exercise 7.2.7

The main idea is that there is telescoping cancelation of the sum $U(f,P) - L(f,P)$ if the subintervals are equal.

#theorem[
  Let $f: [a,b] -> RR$ be increasing on the set $[a,b]$ (i.e., $f(x) <= f(y)$ whenever $x < y$). Then $f$ is integrable on $[a,b]$.
]
#proof[
  If $b=a$ then the theorem is trivial so we will assume $b > a$.
  
  Let $epsilon > 0$ be given and let $n$ be any integer satisfying
  $
    n > ((f(b) - f(a)) (b-a))/epsilon .
  $
  This $n$ must be positive because $f(b) >= f(a)$.

  Consider the partition $P$ with $n$ equal subintervals. On each subinterval $[x_(k-1), x_k]$, the function has its supremum at $x_k$ and its infimum at $x_(k-1)$ because $f(x_k) >= f(x)$ for all $x <= x_k$, and $f(x_(k-1)) <= f(x)$ for all $x >= x_(k-1)$. So the supremum of one subinterval is the infimum of the next.

  Also, because the subintervals are equal, let $Delta x = x_k - x_(k-1) = (b-a)/n$ be the common length of all subintervals.

  Then
  $
    U(f,P) - L(f,P) = & sum_(k=1)^n (M_k - m_k) Delta x \
    = & Delta x (M_1 - m_1 + M_2 - m_2 + ... + M_n - m_n) \
    = & Delta x (M_n - m_1) \
    = & Delta x (f(b) - f(a)) \
    = & (b-a)/n (f(b) - f(a)) \
    < & epsilon .
  $

  Since $f(a) <= f(x) <= f(b)$ for $x in [a,b]$, the function is bounded, so Theorem 7.2.8 applies. Since $epsilon > 0$ was arbitrary and we have exhibited a partition with $U(f,P) - L(f,P) < epsilon$, the function is integrable.
]

= Problem 7: Riemann-integrability of Dirichlet's function
Is Dirichlet's function from Section 4.1 integrable? (It's the function g defined on p. 112.)
#theorem[
  Dirichlet's function, defined as
  $
    g(x) = cases(
      1 "if" x in QQ,
      0 "if" x in.not QQ
    )
  $
  is not Riemann-integrable on any interval $[a,b]$ of $RR$ with $b > a$.
]
#proof[
  Let $P$ be any partition of $[a,b]$ and let $A = [x_(k-1), x_k]$ be any subinterval of $P$. (The subinterval exists and $x_k > x_(k-1)$ because $b > a$). By the density of both the rationals and irrationals in $RR$, there exists a rational number $q in A$ and an irrational number $p in A$.

  Let
  $
    m_k = inf{g(x): x in [x_(k-1), x_k]}
  $
  and
  $
    M_k = sup{g(x): x in [x_(k-1), x_k]} .
  $

  Then $m_k <= 0$ since $g(p) = 0$, but because $0 <= g(x) <= 1$ for all $x$ we have $m_k = 0$. Similarly, $M_k = 1$ because $g(q) = 1$. Thus the lower sum $L(g,P) = 0$ and the upper sum $U(g,P) = sum_(k=1)^n (x_k - x_(k-1)) = b-a$. That is, they don't depend on the particular partition $P$. Hence upper integral of $g$,
  $
    U(g) = inf{U(g,P): P in cal(P)} = inf{b-a} = b-a
  $
  and similarly $L(g) = 0$. So $U(g) eq.not L(g)$, that is, $g$ is not Riemann-integrable.
]
