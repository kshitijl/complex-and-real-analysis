#set page(numbering: "1")
#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let lemma = thmbox("lemma", "Lemma", base: none)
#let theorem = thmbox("theorem", "Theorem", base: none)
#let proof = thmproof("proof", "Proof")
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

= Problem 1: Every convergent sequence is Cauchy

== Proof idea

Get both $x_n$ and $x_m$ within $frac(epsilon,2)$ of the limit $x$, then apply the triangle inequality.

== Proof

#theorem[
  Every convergent sequence is a Cauchy sequence.
]
#proof[
  Let $(x_n)$ be a sequence of real numbers converging to a limit $x in RR$. To prove that it's Cauchy, for any given $epsilon > 0$ we must find an $N in NN$ such that $abs(x_m - x_n) < epsilon$ whenever $m,n >= N$.

  By convergence of $(x_n)$ there exists an $N in NN$ such that $abs(x_n-x) < frac(epsilon,2)$ for every $n >= N$. Then apply the triangle inequality to $x_n - x_m = x_n-x+x-x_m$:
  $
    abs(x_n-x_m) = abs(x_n - x + x - x_m) <= abs(x_n - x) + abs(x - x_m) < frac(epsilon,2) + frac(epsilon,2) = epsilon
  $
  whenever $m,n >= N$.
]

= Problem 2: Give example or prove non-existence of sequences with certain properties

== (a) A Cauchy sequence that is not monotone

A cheap way to do this is to take a monotone sequence and just stick a number in front that makes it not monotone:
$
  a_n = cases(
    0         & "if" n = 1,
    frac(1,n) & "otherwise"
  )
$

But we can also give a sequence that is not monotone even after dropping any finite prefix:
$
  a_n = (-1)^n frac(1,n)
$

This sequence converges to 0 because
$
  abs(a_n - 0) = abs((-1)^n frac(1,n)) = frac(1,n)
$
so by taking $N = 1 + ceil(frac(1,epsilon))$ in the definition of convergence, it converges to 0. And every convergent sequence is Cauchy, by Problem 1.

== (b) A Cauchy sequence with an unbounded subsequence

No such sequence exists.

#theorem[
  Every subsequence of a Cauchy sequence is bounded.
]
#proof[
  Every Cauchy sequence is convergent, by the Cauchy criterion. Every subsequence of a convergent sequence converges to the same limit, proved two problem sets ago. And every convergent sequence is bounded, proved last problem set. Therefore every subsequence of a Cauchy sequence is bounded.
]

Actually we can avoid appealing to the difficult/deep Cauchy criterion:
#proof[
  Every Cauchy sequence is bounded (finite prefix + infinite tail that's within $epsilon$ of $x_N$). And every subsequence of a bounded sequence is bounded, by definitions of bounded and subsequence.
]

== (c) A divergent monotone sequence with a Cauchy subsequence

No such sequence exists.

#theorem[
  Every monotone sequence with a Cauchy subsequence converges.
]
#proof[
  We will prove that the parent sequence is bounded. Then by the Monotone Convergence Theorem, it converges.

  Let $(x_n)$ be a monotone sequence with a Cauchy subsequence $(x_n_k)$. Without loss of generality, let $(x_n)$ be increasing. The subsequence is therefore bounded. Let $M = sup({x_n_k: k in NN})$.

  Every term in the original sequence has a term in the subsequence that comes after it. More precisely, for every $n in NN$, we can find a $n_k >= n$ by taking $k = n$. Since the sequence is monotone increasing,
  $
    x_n <= x_n_n
  $
  for every $n in NN$. But the subsequence is bounded, so
  $
    x_n <= x_n_n <= M .
  $
  So $(x_n)$ is bounded, and therefore converges.
]

== (d) An unbounded sequence containing a subsequence that is Cauchy

Take
$
  a_n = cases(
    n         & "if" n "is odd",
    frac(1,n) & "if" n "is even"
  )
$

so that the even indices form a Cauchy subsequence, while the odd indices are unbounded, making the sequence itself unbounded.

= Problem 3: Direct proofs that the sum and product of two Cauchy sequences are Cauchy

== (a) Sum

=== Proof idea

Get both sequences within $frac(epsilon,2)$ by taking the maximum of $N_x$ and $N_y$, then apply the triangle inequality.

=== Proof

#theorem[
  Let $(x_n)$ and $(y_n)$ be two Cauchy sequences. Then $(x_n + y_n)$ is Cauchy.
]
#proof[
  We are given $epsilon > 0$ and must produce $N in NN$ such that $abs(x_n + y_n - (x_m+y_m)) < epsilon$ whenever $m,n >= N$.

  Let $N_x in NN$ be the index such that $abs(x_n-x_m) < frac(epsilon,2)$ whenever $m,n >= N_x$, and similarly $N_y$. Let $N = max(N_x,N_y)$. Then, whenever $n,m >= N$, we have
  $
    & abs(x_n + y_n - (x_m + y_m)) \
    & = abs((x_n-x_m) + (y_n-y_m)) \
    & <= abs(x_n-x_m) + abs(y_n-y_m) \
    & < frac(epsilon,2) + frac(epsilon,2) \
    & = epsilon
  $
  as desired.
]

== (b) Product

=== Proof idea

Add and subtract $x_n y_m$, factor out, then use the fact that Cauchy sequences are bounded to replace variable terms with the bounds.

=== Proof

#theorem[
  Let $(x_n)$ and $(y_n)$ be two Cauchy sequences. Then $(x_n y_n)$ is Cauchy.
]
#proof[
  Cauchy sequences are bounded (finite prefix + infinite tail that's within $epsilon$ of $x_N$), so let $M_x$ and $M_y$ be any bounds for $(x_n)$ and $(y_n)$ respectively. We may assume that the bounds are nonzero because otherwise at least one of the sequences would be identically zero and the theorem is trivial.

  Let $epsilon > 0$ be given. By definition of Cauchy sequence, there exists $N_x in NN$ such that $abs(x_n-x_m) < frac(epsilon,2 abs(M_y))$ whenever $m,n >= N_x$. Similarly, take $N_y$ to get terms of $(y_n)$ within $frac(epsilon,2 abs(M_x))$ of each other.

  Let $N = max(N_x,N_y)$.

  Then, whenever $m,n >= N$ we have
  $
    &   abs(x_n y_n - x_m y_m) \
    & = abs(x_n y_n - x_n y_m + x_n y_m - x_m y_m) \
    & <= abs(x_n y_n - x_n y_m) + abs(x_n y_m - x_m y_m) \
    & = abs(x_n) abs(y_n - y_m) + abs(y_m) abs(x_n - x_m) \
    & <= abs(M_x) abs(y_n - y_m) + abs(M_y) abs(x_n - x_m) \
    & < abs(M_x) frac(epsilon, 2 abs(M_x)) + abs(M_y) frac(epsilon, 2 abs(M_y)) \
    & = frac(epsilon,2) + frac(epsilon,2) \
    & = epsilon
  $

  as desired.
]

= Problem 4: Equivalence of different characterizations of completeness

=== (a) Bolzano-Weierstrass $=>$ Monotone Convergence without using Archimedean Property

==== Proof idea

Use Bolzano-Weierstrass to get a convergent subsequence, then sandwich every term $x_n$ of the sequence between two terms of the subsequence: the first one after which the subsequence is within $epsilon$ of its limit, and some term of the subsequence that comes after $x_n$.

==== Proof

#theorem[
  If a sequence is monotone and bounded, then it converges.
]
#proof[
  Let $(x_n)$ be a monotone and bounded sequence. Without loss of generality, let it be an increasing sequence.

  By Bolzano-Weierstrass (_every bounded sequence contains a convergent subsequence_), it contains a convergent subsequence $(x_n_k)$, converging to some $x in RR$.

  Given $epsilon > 0$, there exists $N in NN$ such that for every $k >= N$ we have $abs(x_n_k - x) < epsilon$.

  Then for every $k>=N$ we have
  $
    &    abs(x_n_k-x) < epsilon \
    & => -epsilon < x_n_k - x < epsilon \
    & => x-epsilon < x_n_k < x+epsilon .
  $

  We will use the left and right sides of this bound below, with different terms $x_n_k$. We will bound each term of $(x_n)$ between the first term of $(x_n_k)$ after $N$, and any term of $(x_n_k)$ that comes after $x_n$.

  Let $M in NN$ be the index of $N$ in the original sequence, i.e., $M = n_N$ and $x_M = x_n_N$. Since $(x_n)$ is monotone increasing, every term of $(x_n)$ after $x_M$ satisfies
  $
    x - epsilon < x_M <= x_n .
  $

  But for every term $x_n$ there is some term $x_n_n$ of $(x_n_k)$ that comes after it, so, again because the sequence is monotone increasing,
  $
    x_n <= x_n_n < x+epsilon .
  $

  Putting these together, we get
  $
    abs(x_n-x) < epsilon
  $
  so the sequence converges.
]

=== (b) Cauchy Criterion $=>$ Bolzano-Weierstrass, using Archimedean Property

==== Proof idea

Recursively split the interval $[-M,M]$ that contains the sequence, always picking a half which has an infinite number of terms. After enough splittings, the size of the interval is less than $epsilon$, and all subsequent terms are trapped within it. The Archimedean property is used to justify that there is a natural number bigger than $log_2(frac(M,epsilon))$.

==== Proof

#lemma[
  If $x, y in [a,b]$ then $abs(x-y) <= b-a$.
]
#proof[
  $
    x <= b

  $
  and
  $
    a <= y => -y <= -a
  $
  so
  $
    x-y <= b-a .
  $

  Similarly,
  $
    y <= b
  $
  and
  $
    a <= x => -x <= -a
  $
  so
  $
    y-x <= b-a
  $
  so
  $
    -(b-a) <= x-y .
  $

  Putting these together,
  $
    -(b-a) <= x-y <= b-a
  $
  so
  $
    abs(x-y) <= b-a .
  $
]

#theorem[
  Every bounded sequence contains a convergent subsequence.
]
#proof[
  Let $(a_n)$ be a bounded sequence so that there exists $M > 0$ satisfying $abs(a_n) < M$ for all $n in NN$. Bisect the closed interval $[-M,M]$ into the two closed intervals $[-M,0]$ and $[0,M]$. (The midpoint is included in both halves.) At least one of these closed intervals contains an infinite number of the terms of the sequence $(a_n)$. Select a half for which this is the case and label that interval as $I_1$. Then, let $a_n_1$ be some term in the sequence $(a_n)$ satisfying $a_n_1 in I_1$.

  Next, we bisect $I_1$ into closed intervals of equal length, and let $I_2$ be a half that again contains an infinite number of terms of the original sequence. Because there are an infinite number of terms from $(a_n)$ to choose from, we can select an $a_n_2$ from the original sequence with $n_2 > n_1$ and $a_n_2 in I_2$. In general, we construct the closed interval $I_k$ by taking a half of $I_(k-1)$ containing an infinite number of terms of $(a_n)$ and then select $n_k > n_(k-1) > ... > n_2 > n_1$ so that $a_n_k in I_k$.

  The length of $I_k$ is $frac("len"(I_(k-1)),2)$ for each $k > 1$ and the length of $I_1$ is $M$, so
  $
    "len"(I_k) = frac(M,2^(k-1)) .
  $
    
  Given an $epsilon > 0$, choose $t in NN$ such that
  $
    t > frac(M,epsilon) .
  $
  Such a $t$ exists by the Archimedean Property and because both $M$ and $epsilon$ are positive real numbers.

  Since $t$ is a natural number there is some power of 2 bigger than it; in other words, the sequence of powers of 2 is unbounded (this is a fact about the natural numbers, not real analysis, and I think we can prove by induction that $2^n >= n$ for all $n in NN$).

  Therefore pick some $N in NN$ such that
  $
    2^(N-1) >= t > frac(M,epsilon)
  $
  so that
  $
    epsilon > frac(M,2^(N-1)) = "len"(I_N) .
  $

  Then for every $i,j >= N$, the terms $a_n_i, a_n_j in I_N$ so by the lemma proved above,
  $
    abs(a_n_i-a_n_j) < epsilon ,
  $
  so by the Cauchy Criterion, the subsequence $(a_n_k)$ converges.
]

=== (c) Archimedean Property $arrow.double.not$ Axiom of Completeness

The field $QQ$ of rational numbers also has the Archimedean property: for every rational $frac(p,q)$, by the Euclidean division algorithm we have
$
  p = q d + r
$
where $0 <= r < q$, so $abs(d) + 1 > frac(p,q)$.

Even more trivially, $abs(p) + 1 > frac(p,q)$.

But we know the rationals do not satisfy the Axiom of Completeness, because the set ${x in QQ: x^2 < 2}$ does not have a least upper bound in $QQ$, because $sqrt(2)$ is irrational. So it cannot be possible to prove the Axiom of Completeness from the Archimedean property.
