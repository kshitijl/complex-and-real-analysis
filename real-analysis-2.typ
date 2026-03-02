#set page(numbering: "1")
#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let lemma = thmbox("lemma", "Lemma", base: none)
#let theorem = thmbox("theorem", "Theorem", base: none)
#let definition = thmbox("definition", "Definition", base: none)
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

Exercises are from Stephen Abbott's _Understanding Analysis_, Second Edition.

= Problem 1: $lim sup$ and $lim inf$
(Exercise 2.4.7)

== (a) If $(a_n)$ is bounded then $y_n = sup {a_k: k >= n}$ converges
=== Proof idea
The sets we're taking $sup$ over form a nested sequence, so the suprema can only become smaller, so $(y_n)$ is monotone and therefore converges.

=== Proof

#lemma[
  Let $A$ and $B$ be two bounded non-empty sets in $RR$. Then
  $
    sup(A union B) = max(sup A,sup B)
  $
]
#proof[
  Let $s = sup(A union B)$, which exists since $A union B$ is nonempty (both $A$ and $B$ are) and bounded by the maximum of bounds of $A$ and $B$.

  By definition,
  $
    s >= x "for every" x in A union B
  $
  so
  $
    s >= x "for every" x in A
  $
  so
  $
    s >= sup A ,
  $
  for if $s < sup A$ then in light of the second inequality above, $sup A$ would not be the _least_ upper bound of $A$.
  By a symmetrical argument,
  $
    s >= sup B
  $
  and therefore
  $
    s >= max(sup A, sup B) .
  $

  Suppose for the sake of contradiction that $s > max(sup A, sup B)$ and let $epsilon = s - max(sup A, sup B) > 0$. Then there must exist some element $x in A union B$ such that
  $
    x > s - epsilon .
  $
  Since $x in A union B$, it must be a member of $A$ or $B$ or both. If it's a member of $A$ then
  $
    x > s - epsilon = max(sup A, sup B) >= sup A ,
  $
  a contradiction of $sup A$ being an upper bound. Similarly if $x in B$ we get a contradiction.

  The only possibility left is $s = max(sup A, sup B)$.
]

#theorem[
  Let $(a_n)$ be any bounded sequence in $RR$. Then the sequence defined by $y_n = sup {a_k: k >= n}$ converges.
]
#proof[
  Let $S_n$ be the set ${a_k: k >= n}$. Then $S_n = {a_n} union S_(n+1)$ for every $n in NN$. By the lemma proved above,
  $
    y_n = sup S_n = max(sup {a_n}, sup S_(n+1)) = max(a_n, y_(n+1)) >= y_(n+1)
  $
  so $(y_n)$ is a decreasing sequence.

  But $(a_n)$ is bounded, therefore bounded below by some $M in RR$. Since $y_n >= a_n$ for every $n in NN$, $y_n >= M$.
  So $(y_n)$ is monotone and bounded, therefore converges.
]

== (b) Defining $lim inf$

#lemma[
  Let $A$ be any non-empty bounded set in $RR$. Then
  $
    sup A = - inf {-x: x in A}  
  $
]
#proof[
  Let $s = sup A$ and $B = {-x: x in A}$.

  Then $s >= x$ for every $x in A$, therefore $-s <= -x$ for every $x in A$, so $-s$ is a lower bound for $B$.

  Let $t$ be another lower bound for $B$ with $t > -s$. Then $-t < s$ and
  $
    t <= -x "for every" x in A
  $
  so
  $
    -t >= x "for every" x in A,
  $
  that is, $-t$ is an upper bound for $A$ but is less than $s$, contradicting the definition of $s$ as the _least_ upper bound.
]

An immediate corollary:
$
  inf A = - sup {-x: x in A}
$
by applying the lemma above to ${-x: x in A}$.

Let $(a_n)$ be any bounded sequence. Define the sequence $x_n = inf {a_k: k >= n}$. Then $x_n = -sup {-a_k: k >= n}$ by the corollary, and therefore converges by the theorem proved before (and the Algebraic Limit Theorem for convergence of $(c a_n)$ with $c=-1$). Since it converges, we may define $lim inf a_n$ to be the limit of this sequence $(x_n)$.

== (c) $lim inf a_n <= lim sup a_n$

#lemma[
  Let $A$ be any non-empty bounded set in $RR$. Then
  $
    inf A <= sup A .
  $
]
#proof[
  Let $t = inf A$ and $s = sup A$. Then, for any $x in A$,
  $
    t <= x <= s 
  $
  since they are lower and upper bounds respectively. The desired result follows.
]

#theorem[
  Let $(a_n)$ be any bounded sequence in $RR$. Then
  $
    lim inf a_n <= lim sup a_n .
  $
]
#proof[
  For each $n in NN$, define the set
  $
    S_n = {a_k: k >= n} 
  $
  and the sequences
  $
    x_n & = inf S_n \
    y_n & = sup S_n .
  $
  Then by the lemma proved above,
  $
    x_n <= y_n "for every" n in NN
  $
  and by the Order Limit Theorem,
  $
    lim inf a_n = lim x_n <= lim y_n = lim sup a_n .
  $
]

The inequality is strict for the sequence
$
  a_n = cases(
    0 "if" n "is odd",
    1 "if" n "is even"
  )
$

since the supremum of any tail of this sequence is 1, and the infimum of any tail is 0.

== (d) $lim inf a_n = lim sup a_n$ iff $lim a_n$ exists

#theorem[
  Let $(a_n)$ be a sequence in $RR$. Then $lim inf a_n = lim sup a_n$ iff $lim a_n$ exists.
]
#proof[
  ($arrow.double.l$) Suppose $(a_n)$ converges to some limit $a$ and let $epsilon$ be given.

  Then there exists some $N in NN$ such that for every $n >= N$,
  $
    |a_n - a| < epsilon/2
  $
  so
  $
    a - epsilon/2 < a_n < a + epsilon/2 .
  $
  Define the set $S_m = {a_k: k >= m}$ and let $s_m = sup S_m$. Then, for every $n >= N$, we have
  $
    s_n >= a_n > a - epsilon/2 > a - epsilon
  $<e1>
  since it is an upper bound.

  Suppose for the sake of contradiction that $s_n > a + epsilon/2$ and let $delta = s_n - (a+epsilon/2) > 0$. Then there must exist some $a_i in S_n$ (and therefore $i >= n$) such that
  $
    a_i > s_n - delta = s_n - (s_n - (a+epsilon/2)) = a + epsilon/2 ,
  $
  a contradiction of the choice of $N$ and $epsilon$. Therefore
  $
    s_n <= a + epsilon/2
  $
  and so
  $
    s_n < a + epsilon .
  $<e2>

  Combining @e1 and @e2, we get
  $
    |s_n - a| < epsilon
  $
  and so the sequence $(s_n)$ converges to $a$, that is, $lim sup a_n = lim a_n$.

  By a similar and symmetric argument, $lim inf a_n = lim a_n$. Therefore $lim inf a_n = lim sup a_n$.

  ($=>$) Suppose $lim inf a_n = lim sup a_n = a$ and let $epsilon$ be given and let the set $S_m$ be defined as above. Then there exists some $N_1 in NN$ such that for every $n >= N_1$,
  $
    a - epsilon < sup S_n < a + epsilon
  $
  but $sup S_n$ is an upper bound for every element $a_i in S_n$, that is, for every $i >= n$, so
  $
    a_n <= sup S_n < a + epsilon
  $
  for every $n >= N_1$. Similarly by convergence of $inf S_n$ to $a$, we have an $N_2 in NN$ such that
  $
    a - epsilon < inf S_n <= a_n
  $
  and the two equations together give
  $
    |a_n - a| < epsilon 
  $
  for $n >= max(N_1,N_2)$.
]

= Problem 2: Cauchy Condensation Test "only if" direction
(Exercise 2.4.9)

#theorem[
  Suppose $(b_n)$ is decreasing and satisfies $b_n >= 0$ for all $n in NN$. Then, if the series
  $
    sum_(n=0)^infinity 2^n b_(2^n) = b_1 + 2 b_2 + 4 b_4 + 8 b_8 + ...
  $
  diverges, then so does $sum_(n=1)^infinity b_n$.
]
#proof[
  Let $c_n = 2^n b_(2^n)$, let $s_n = sum_(i=1)^n b_i$ be the sequence of partial sums of $(b_n)$ and let $t_n = sum_(i=0)^n c_i$ (note the 0 lower bound!) be the sequence of partial sums of $(c_n)$.

  We have
  $
    s_(2^n) = sum_(i=1)^(2^n) b_i
    & = b_1 + b_2 + b_3 + b_4 + b_5 + b_6 + b_7 + b_8 + ... + b_(2^n) \
    & = b_1 + b_2 + (b_3 + b_4) + (b_5 + b_6 + b_7 + b_8) + ... + b_(2^n) \
    & >= b_1 + b_2 + (b_4 + b_4) + (b_8 + b_8 + b_8 + b_8) + ... + (b_(2^n) + ... + b_(2^n)) \

    & = b_1 + b_2 + 2 b_4 + 4 b_8 + ... + 2^(n-1) b_(2^n) \
    & = b_1/2 + frac(b_1 + 2 b_2 + 4 b_4 + 8 b_8 + ... + 2^n b_(2^n),2) \
    & >= frac(b_1 + 2 b_2 + 4 b_4 + 8 b_8 + ... + 2^n b_(2^n),2) \
    & = t_n / 2
  $

  Since $b_n >= 0$, the terms $c_n = 2^n b_(2^n) >= 0$ as well and so the partial sums $t_n$ are increasing. The series diverges, therefore by the Monotone Convergence Theorem the partial sums $t_n$ must be unbounded. Since $s_(2^n) >= t_n/2$, the sequence of partial sums $s_n$ is also unbounded. But all convergent sequences are bounded, so $(s_n)$ diverges.
]

= Problem 3: Three Proofs of the Alternating Series Test
(Exercise 2.7.1)

#theorem[
  Let $(a_n)$ be a sequence satisfying,

  (i) $a_1 >= a_2 >= a_3 >= ... >= a_n >= a_(n+1) >= ...$ and 

  (ii) $(a_n) -> 0$.

  Then, the alternating series $sum_(n=1)^infinity (-1)^(n+1)a_n$ converges.
]

The following definitions will come in handy in all the proofs below:
#definition[
Let
$
  s_n = a_1 - a_2 + a_3 - ... plus.minus a_n
$
define the sequence of partial sums of $(a_n)$.
]

#definition[
  Let
$
  p_i = a_i - a_(i+1) >= 0
$
since $a_i >= a_(i+1)$ for all $i in NN$.
]

The following fact will come in handy:

#lemma[
  Given the hypotheses above, $a_n >= 0$ for every $n in NN$.
]
#proof[
  Suppose for the sake of contradiction that some $a_i < 0$. Let $epsilon = -a_i > 0$ and $N$ the corresponding index in the definition of sequence convergence. Then for some $m >= max(i,N)$ we must have
  $
    & |a_m - 0| < epsilon \
    => & - epsilon < a_m - 0 < epsilon \
    => & -(-a_i) < a_m \
    => & a_i < a_m ,
  $
  which contradicts that $(a_n)$ is decreasing.
]

== (a) Using the Cauchy Criterion
=== Proof idea
Bound
$
  abs(a_(m+1) - a_(m+2) + ... plus.minus a_n)
$
by $|a_(m+1)|$ by grouping terms in pairs and arguing that each $-a_(m+i) + a_(m+i+1) <= 0$, then group the other way to show that the sum is always non-negative.

I tried to arrange things to reduce ugly casework but still ended up with some. There are ultimately four cases that must be handled: $m$ can be odd or even, and $n-m$ can be odd or even. 

=== Proof
#proof[
  Since $(a_n) -> 0$, for every $epsilon > 0$ there exists some $N in NN$ such that whenever $m >= N$, $|a_m| < epsilon$.

  Let $n > m >= N$ and $n-m$ be odd.

  Then
  $
       & a_(m+1) - a_(m+2) + a_(m+3) - a_(m+4) + a_(m+5) ... - a_(n-1) + a_n \
     = & p_(m+1) + p_(m+3) + ... + p_(n-2) + a_n \
     >= 0
  $ <e3>
  since every $p_i >= 0$ and every $a_n >= 0$.

  Now grouping the other way we see that
  $
       & a_(m+1) - a_(m+2) + a_(m+3) - a_(m+4) + a_(m+5) ... - a_(n-1) + a_n \
     = & a_(m+1) - (a_(m+2) - a_(m+3)) - (a_(m+4) - a_(m+5)) ... - (a_(n-1) - a_n) \
     = & a_(m+1) - p_(m+2) - p_(m+4) ... - p_(n-1) \
    <= & a_(m+1)
  $ <e4>
  since every $p_i >= 0$. @e3 justifies taking the absolute value of both sides of @e4 to get
  $
       |a_(m+1) - a_(m+2) + a_(m+3) - a_(m+4) + a_(m+5) ... - a_(n-1) + a_n| <= |a_(m+1)| < epsilon
  $
  where the last inequality follows from convergence of $(a_n)$ to 0.

  If $n-m$ is even then much the same happens except the dangling $a_n$ must be handled in the equivalent of @e4 instead. Writing out both sides in full:
  $
       & a_(m+1) - a_(m+2) + a_(m+3) - a_(m+4) + a_(m+5) ... + a_(n-1) - a_n \
     = & p_(m+1) + p_(m+3) + ... + p_(n-1) \
     >= 0
  $
  and
  $
       & a_(m+1) - a_(m+2) + a_(m+3) - a_(m+4) + a_(m+5) - ... - a_(n-2) + a_(n-1) - a_n \
     = & a_(m+1) - (a_(m+2) - a_(m+3)) - (a_(m+4) - a_(m+5)) - ... - (a_(n-2) - a_(n-1)) - a_n \
     = & a_(m+1) - p_(m+2) - p_(m+4) ... - p_(n-2) - a_n \
    <= & a_(m+1) - a_n \
    <= & a_(m+1)
  $
  where the last step follows since $a_n >= 0$.

  Depending on the parity of $m$, $s_n - s_m = plus.minus (a_(m+1) - a_(m+2) + a_(m+3) - ... plus.minus a_n)$. In all cases,
  $
       & abs(s_n - s_m) = abs(plus.minus(a_(m+1) - a_(m+2) + a_(m+3) - ... plus.minus a_n)) \
    =  & abs(a_(m+1) - a_(m+2) + a_(m+3) - ... plus.minus a_n) \
    <= & abs(a_(m+1)) \
    <= & epsilon
  $
  proving convergence by the Cauchy Criterion for Series.  
]

== (b) Using the Nested Interval Property

=== Proof idea

Successive pairs of partial sums form nested intervals $[s_(2n), s_(2n-1)]$ with vanishing diameter, and the tail of the sequence of partial sums is contained in each interval. So there's a unique point in the intersection.

This situation is similar to the proof that nested compact sets in $CC$ with vanishing diameter contain a unique point.

=== Proof

#proof[
  Observe that
  $
    s_(2n) = s_(2n-1) - a_(2n) <= s_(2n-1)
  $ <e5>
  so we may define the sequence of intervals
  $
    I_n = [s_(2n), s_(2n-1)] .
  $

  We group the terms of $s_(2n+1)$ like so:
  $
    s_(2n+1)
    = & a_1 - a_2 + ... - a_(2n-2) + a_(2n-1) - a_(2n) + a_(2n+1) \
    = & [a_1 - a_2 + ... - a_(2n-2) + a_(2n-1)] - (a_(2n) - a_(2n+1)) \
    = & s_(2n-1) - p_(2n) \
    <= & s_(2n-1)
  $ <e6>
  and similarly for $s_(2n+2)$ we have
  $
    s_(2n+2)
    = & a_1 - a_2 + ... + a_(2n-1) - a_(2n) + a_(2n+1) - a_(2n+2) \
    = & [a_1 - a_2 + ... + a_(2n-1) - a_(2n)] + (a_(2n+1) - a_(2n+2)) \
    = & s_(2n) + p_(2n+1) \
    >= & s_(2n)
  $ <e7>
  so that
  $
    I_(n) supset.eq I_(n+1)
  $
  for every $n in NN$. Therefore, since $s_(2n) in I_n$ and $s_(2n-1) in I_n$, for every $m >= 2n$ we have $s_m in I_n$. (Because if $m$ is even then $s_m in I_(m/2)$ and if $m$ is odd then $s_m in I_((m+1)/2)$, and both of those are contained in $I_n$.)

  By the Nested Interval Property, the sequence $I_n$ has nonempty intersection. Pick any point $a in inter_(n=1)^infinity I_n$.

  The length of $I_n$ is $s_(2n-1) - s_(2n) = a_(2n)$, which goes to 0. Let $epsilon$ be given and pick $N$ such that $|a_(2N)| < epsilon$. Then for every $m >= 2N$ we have
  $
    s_m in I_N
  $
  and
  $
    a in I_N
  $
  therefore, by the lemma proved before about points in the same interval (Real Analysis Problem Set 1, Problem 4, Lemma 1), we have
  $
    abs(s_m - a) <= s_(2N-1) - s_(2N) = a_(2N) < epsilon .
  $
]

== (c) Using the Monotone Convergence Theorem

=== Proof idea

The even partial sums are monotone increasing and bounded above by every odd partial sum. The odd partial sums are monotone decreasing and bounded below by every even partial sum. So by the Monotone Convergence Theorem, both subsequences converge. But the difference between them is just a member of $(a_n)$, which converges to 0. So the two limits are equal.

=== Proof

#proof[
  In @e6 we proved that $s_(2n+1) <= s_(2n-1)$, so the sequence $s_(2n+1)$ is decreasing and bounded above by $s_1 = a_1$:
  $
    s_(2n+1) <= s_(2n-1) <= ... <= s_3 <= s_1 = a_1
  $

  Also, by @e5, $s_(2n) <= s_(2n-1)$, but $s_(2n-1) <= a_1$, so the sequence $(s_2n)$ is also bounded above by $a_1$.

  By exactly symmetric reasoning, by @e7, the sequence $s_(2n)$ is increasing, and both $(s_(2n))$ and $(s_(2n+1))$ are bounded below by $s_2 = a_1 - a_2$.

  Therefore, both sequences are monotone and bounded, so by the Monotone Convergence Theorem, they both converge.

  Their difference is $s_(2n+1) - s_(2n) = a_(2n+1)$, which is given to converge to 0. Therefore by the Algebraic Limit Theorem, both sequences converge to the same limit $a$. Since any term of $(s_n)$ must belong to exactly one of the two sequences, it may be brought arbitrarily close to $a$, so $(s_n)$ converges.

  To spell it out in explicit detail: given $epsilon$, pick $N = max(N_1,N_2)$ where $N_1$ is large enough that $abs(s_(2n) - a) < epsilon$ for $n >= N_1$ and $N_2$ large enough that $abs(s_(2n+1) - a) < epsilon$ for $n >= N_2$. Then $abs(s_m - a) < epsilon$ for all $m >= 2N$.
]

= Problem 4: Two Proofs of the Comparison Test
(Exercise 2.7.3)

#theorem[
  Assume $(a_k)$ and $(b_k)$ are sequences satisfying $0 <= a_k <= b_k$ for all $k in NN$.

  (i) If $sum_(k=1)^infinity b_k$ converges, then $sum_(k=1)^infinity a_k$ converges.

  (ii) If $sum_(k=1)^infinity a_k$ diverges, then $sum_(k=1)^infinity b_k$ diverges.
]

== (a) Using the Cauchy Criterion for Series
=== Proof idea
That $b_k >= a_k$ leads directly to
$
  abs(b_(m+1) + b_(m+2) + ... + b_n) >= abs(a_(m+1) + a_(m+2) + ... + a_n) 
$
which is exactly what we need to apply the Cauchy Criterion for Series.

=== Proof
#proof[
  Since $b_k >= a_k$ for all $k$, for any $n > m$, we have
  $
    (b_(m+1) - a_(m+1)) + (b_(m+2) - a_(m+2)) + ... + (b_n - a_n) >= 0
  $
  so
  $
    b_(m+1) + b_(m+2) + ... + b_n >= a_(m+1) + a_(m+2) + ... + a_n .
  $
  Since $b_k >= 0$ and $a_k >= 0$ for all $k$, both sides above are positive and we may take absolute values:
  $
    abs(b_(m+1) + b_(m+2) + ... + b_n) >= abs(a_(m+1) + a_(m+2) + ... + a_n) .
  $ <e8>

  Suppose $sum_(k=1)^infinity b_k$ converges. By the Cauchy Criterion for Series, given any $epsilon$, we may find an $N in NN$ such that the LHS of @e8 is smaller than it for any $n > m >= N$. Therefore the RHS is also bounded, and therefore by the Cauchy Criterion for Series applied in the opposite direction, $sum_(k=1)^infinity a_k$ converges.

  Suppose $sum_(k=1)^infinity a_k$ diverges. Then, by the Cauchy Criterion for Series, there exists some $epsilon$ such that for every $N in NN$ there are some $n > m >= N$ for which the RHS of @e8 is $ >= epsilon$. Therefore the LHS is also $ >= epsilon$ for the same choice of $epsilon$ and the same choice of $m,n$ for each $N$. Therefore $sum_(k=1)^infinity b_k$ diverges.
]

== (b) Using the Monotone Convergence Theorem
=== Proof idea
The terms of both sequences are positive, so the partial sums of both are monotone increasing. If the bigger one converges then it's bounded and so bounds the smaller one; if the smaller one diverges then it must be unbounded (otherwise it would converge) and so pushes the bigger one to unboundedness.

=== Proof
#proof[
  Let $(s_n)$ be the sequence of partial sums of $(a_n)$, and $(t_n)$ the sequence of partial sums of $(b_n)$.
  
  Since $a_k >= 0$,
  $
    s_(n+1) = s_n + a_(n+1) >= s_n ,
  $
  so $(s_n)$ is a monotone increasing sequence and $s_n >= 0$ for all $n in NN$. Similarly, $(t_n)$ is also monotone increasing and $t_n >= 0$ for all $n in NN$.

  Also,
  $
    t_n - s_n = sum_(i=1)^n (b_i - a_i) >= 0
  $
  since each term $b_i - a_i >= 0$. So $t_n >= s_n$ for every $n in NN$.

  If $(t_n)$ converges then it is bounded. Call that bound $M in RR$. Then for every $n in NN$,
  $
    0 <= s_n <= t_n <= M ,
  $
  so $(s_n)$ is bounded, and since it is also monotone, it converges.

  Now suppose that $(s_n)$ diverges. Since it is monotone, it must be unbounded, since if it were bounded it would converge. So for every $M in RR$ there exists some $N in NN$ such that
  $
    |s_N| > |M|
  $
  but $s_n >= 0$ for all $n in NN$ so
  $
    0 <= |M| < s_N <= t_N ,
  $
  so $(t_n)$ is unbounded and therefore diverges.
]

= Problem 5: Convergence of $sum_(n=1)^infinity 1 slash n^p$
(Exercise 2.7.5)
== Proof idea
Apply the Cauchy Condensation Test; it turns the difficult-looking $frac(1,n^p)$ into a tractable $frac(2^n,2^(n p))$.

== Proof
#theorem[
  The series $sum_(n=1)^infinity 1 slash n^p$ converges if and only if $p > 1$.
]
#proof[
  By the Cauchy Condensation Test, the series in question converges iff
  $
    sum_(n=1)^infinity 2^n 1/(2^n)^p
  $
  does. Some algebra turns it into
  $
    sum_(n=1)^infinity (2^(1-p))^n
  $
  which is a geometric series with $r = 2^(1-p)$, which therefore converges iff $|r| < 1$. Since $2^x$ is positive for all $x in RR$

  [Note to Nic: I guess we're doing foundational real analysis here, so it's unclear to me if we can talk yet about $2^x$ for non-integer $x$ and use properties like "$2^x > 0$". I suppose we could define it as the limit of $2^(p/q)$ for some sequence of rational numbers that converges to $x$, or as $e^(x log(2))$, but either way we'd have some proving to do I think? And perhaps some difficult stuff lurks there? For example that every sequence of rationals converging to $x$ yields the same value for $2^x$, or that such a number as $log 2$ exists, or even that $(2^a)^b = 2^(a b)$, which oops, ha ha, I'm now realizing I used above. Now I will proceed as if all this never occurred to me la dee da and I'm just a happy plug-n-chug student of math from the early 19th century or before.]

  we may drop the absolute value and just say
  $
    2^(1-p) < 1
  $
  which happens iff

  [Uh oh! _Can_ we use this as a property of the exponential function yet? This whole proof goes through just fine if $p in ZZ$ or even if $p in QQ$ though.]

  $
    1-p < 0 ,
  $
  i.e., iff
  $
    p > 1 .
  $
]

= Problem 6: One Proof of the Ratio Test
(Exercise 2.7.9)

Given a series $sum_(n=1)^infinity a_n$ with $a_n != 0$, the Ratio Test states that if $(a_n)$ satisfies
$
  lim abs(frac(a_(n+1),a_n)) = r < 1,
$
then the series converges absolutely.

=== Proof idea

Drop a finite prefix, then use comparison test against a geometric series whose common ratio is $r$ plus a little bit (but not so much it's bigger than 1).

== (a) 
Given $r < r' < 1$, pick $epsilon = r'-r > 0$ in the definition of sequence convergence of $abs(frac(a_(n+1), a_n))$ to get that there exists an $N in NN$ such that for any $n >= N$,
$
  abs(abs(frac(a_(n+1), a_n)) - r) < epsilon
$
so
$
  -epsilon < frac(abs(a_(n+1)), abs(a_n)) - r < epsilon = r' - r .
$
Adding $r$ to both sides of the second of these two inequalities, we find that
$
  frac(abs(a_(n+1)), abs(a_n)) < r'
$
and since $abs(a_n) > 0$ we are justified in multiplying by it to obtain
$
  abs(a_(n+1)) < abs(a_n) r'
$
as desired.

== (b)
Since every term of the sequence $abs(frac(a_(n+1), a_n)) >= 0$ and $r$ is its limit, by the Order Limit Theorem, $r >= 0$. Then, since $0 <= r < r' < 1$, we have
$
  abs(r') < 1
$ 
so the geometric series
$
  sum_(n=1)^infinity (r')^n
$
converges.

Since $abs(a_N)$ is just a fixed number, by the Algebraic Limit Theorem, $abs(a_N) sum (r')^n$ converges.

== (c)

Let $N$ be chosen as in part (a). Then for any $n >= N$ we have
$
  abs(a_(n+1)) < abs(a_n) r' .
$ <e9>
Multiplying both sides of this inequality by the positive quantity $r'$, we see that
$
  abs(a_(n+1)) r' < abs(a_n) (r')^2 .
$
But since @e9 applies for _any_ $n >= N$, we may apply it for $n+1$ to the LHS above to get
$
  abs(a_(n+2)) < abs(a_(n+1)) r' < abs(a_n) (r')^2 .
$
Continuing in this way, by repeated multiplication with $r'$ and application of @e9, we have
$
  abs(a_(n+m)) < abs(a_n) (r')^m 
$ <e10>
for $m >= 1$.

Pick $n=N$ in the inequality above and write 
$
  sum_(n=1)^infinity abs(a_n) = sum_(n=1)^N abs(a_n) + sum_(n=N+1)^infinity abs(a_n) = 
sum_(n=1)^N abs(a_n) + sum_(m=1)^infinity abs(a_(N+m))
$
where the final expression consists of a finite sum plus a series, which converges by the Comparison Test: @e10 shows that each term is less than the corresponding term of the series $abs(a_N) sum (r')^n$, shown to converge in (b).

Since the series converges absolutely, it converges.

= Bonus 1: Root Test
I saw this used in Complex Analysis a few times (I think to say things about the radius of convergence of power series) and I always wondered where it came from. Now I think I have the tools to prove it. I know there are more general versions of this test that don't assume the existence of the limit, but I'll limit myself to this simpler version for now.

== Proof idea

Same idea as the ratio test: drop a finite prefix, then use comparison test against a geometric series whose common ratio is $r$ plus a little bit (but still smaller than 1).

If $r > 1$ then the individual terms just don't go to 0 like they need to for a convergent series.

== Proof

#theorem[
  Let $(a_n)$ be a sequence such that the limit
  $
    lim abs(a_n)^(1 slash n) = r
  $
  exists. Then the series $sum_(n=1)^infinity a_n$ is absolutely convergent when $r<1$ and divergent when $r>1$.
]
#proof[
  If $r<1$ then we may pick $0 <= r < r' < 1$ and set $epsilon = r'-r$ in the definition of convergence to get that there exists an $N in NN$ such that for every $n >= N$ we have
  $
    - epsilon < abs(a_n)^(1 slash n) -r < epsilon
  $
  so
  $
    abs(a_n)^(1 slash n) < r'
  $
  so
  $
    abs(a_n) < (r')^n .
  $ <e11>

  Now write 
  $
    sum_(n=1)^infinity abs(a_n) = sum_(n=1)^N abs(a_n) + sum_(n=N+1)^infinity abs(a_n)
  $
  which is a finite sum plus a series that converges by the Comparison Test: @e11 shows that each term is less than the corresponding term of the geometric series $sum (r')^n$, which converges since $0 < r' < 1$. So $sum_(n=1)^infinity a_n$ converges absolutely.

  If, on the other hand, $r>1$ then set $epsilon=r-1 > 0$ in the definition of convergence to obtain that there exists some $N in NN$ such that for every $n >= N$,
  $
    -epsilon < abs(a_n)^(1 slash n) - r
  $
  so
  $
    r - epsilon < abs(a_n)^(1 slash n)
  $
  so
  $
    1 < abs(a_n) 
  $
  which proves that $(a_n)$ does not converge to 0, but the terms of any convergent series converge to 0. So $sum_(n=1)^infinity a_n$ diverges.
]

= Bonus 2: Commentary on the proof that an absolutely convergent series may be rearranged
There's a slightly tricky step in the proof that Abbott glides past with "It should now be evident that ...". Sadly for me it was not so trivially evident.

Let $(a_n)$ be the original sequence.

Let $(b_n)$ be the rearranged sequence.

Let $s_n$ be the $n$'th partial sum of the $(a_n)$, and let $A$ be its limit. So $A$ is the sum that $sum_(n=1)^infinity a_n$ converges to.

Let $t_n$ be the $n$'th partial sum of the $(b_n)$.

We want to bound $abs(t_n - A)$ for $n$ big enough.
We start by adding and subtracting $s_N$ to get
$
  abs(t_n - A) <= abs(t_n - s_N) + abs(s_N - A) .
$

Now, $abs(s_N-A)$ is easy to bound because $A$ is exactly what $(s_n)$ converges to. It remains to bound $abs(t_n - s_N)$: the difference between the partial sum of the rearranged sequence and the partial sum of the original sequence.

Here's the slightly interesting/tricky/confusing part:

Look at what $t_n - s_N$ is. It's $b_1 + b_2 + ... - (a_1 + a_2 + ...)$.

We could try applying the triangle inequality:
$
  abs(t_n - s_N) <= |b_1| + |b_2| + ... + |b_n| + |a_1| + |a_2| + ... + |a_N| .
$

But that doesn't really help: while we know that $|a_1| + |a_2| + ...$ is bounded and converges, it doesn't converge to something arbitrarily tiny. Which is what we need to prove about $abs(t_n - s_N)$. And similarly, while we could prove that $|b_1| + |b_2| + ...$ converges to $|a_1| + |a_2| + ...$ , that wouldn't help us because again, it doesn't have to be tiny.

Hmm. Very sad.

However! We _do_ have a guarantee that the _tail_ $|a_N| + |a_(N+1)| + ...$ can be made arbitrarily small. (How do we know that? By Cauchy Criterion for Series: this tail is the difference between two partial sums, so it can be made as small as we like.)

And because all the terms in this tail are positive, we're not relying on cancelation to make the tail arbitrarily small. We're allowed to take a subset of the terms, and that's still guaranteed to become arbitrarily small, as long as we go far enough into the sequence $(a_n)$ before we start adding up these terms $|a_n|$. 

Let "far enough" be $N$.

Now how can we turn $|t_n - s_N|$ into something that only has this tail? We gotta get rid of all terms of $(a_n)$ before $a_N$. We have a minus sign there to work with.

Here's the main idea: go far enough into the sequence $b_n$ (call "far enough" = $M$) such that its partial sum $t_M$ has ALL the terms of $a_n$ before $a_N$. They will cancel each other out. What will be left? A subset of terms of the sequence $a_n$ that all show up _after_ $a_N$, so they are in the tail that we can make arbitrarily small.

So when we apply the triangle inequality to $|t_M - s_N|$ now, we get some subset of the terms $|a_(N+1)| + |a_(N+2)| + ...$, which _can_ be made arbitrarily small.

So our final answer to the challenge "Here's epsilon! Can you make the partial sum $t_n$ close enough to $A$?" is "Yes, take $M$ terms of $b_n$ to form the partial sum $t_M$. Where $M$ is far enough out into $b_n$ such that the first $N$ terms of $a_n$ have appeared. Where $N$ is far enough out into $a_n$ such that its tail $|a_N| + |a_(N+1)| + ...$ is smaller than $epsilon/2$, and also far enough out that its partial sum $s_N$ is within $epsilon/2$ of $A$, where $N$ is big enough to satisfy both these conditions."

Where does this proof fail if the rearrangement function isn't injective? Then multiple terms $b_n$ could map to the same terms of $a_n$, and we'd have extra copies of terms of $(a_n)$ in $t_M$ that wouldn't get canceled out by $s_N$. Thus, early (and thus potentially large) terms of $(a_n)$ could still remain in $abs(t_M - s_N)$ no matter how far out into $(b_n)$ we go.

Where does it fail if it's not surjective? Then some of the $a_n$ could be missing from the $b_n$, and there's no guarantee we'd be able to go far enough out into $b_n$ to get all the $a_n$, and thus get the cancelation we need.

Where does it fail if $(a_n)$ isn't absolutely convergent? Then we don't have a bound on the tail $|a_(N+1)| + |a_(N+2)| + ...$ that we get after applying the triangle inequality to what remains of $|t_m - s_N|$ after cancelation.
