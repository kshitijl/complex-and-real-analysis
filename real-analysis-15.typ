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

= Problem 1: Thomae's function is integrable
Exercise 7.3.2

Let
$
  t(x) = cases(
    1 & "if" x = 0,
    1 slash n quad & "if" x = m slash n in QQ backslash {0} "is in lowest terms with" n > 0,
    0 & "if" x in.not QQ .
  )
$

The function has a countable set of discontinuities occurring at precisely every rational number.

== (a)

#lemma[
  $L(t,P) = 0$ for any partition $P$ of $[0,1]$.
]
#proof[
  Let $P$ be any partition of $[0,1]$ and $[x_(k-1), x_k]$ be its $k$'th subinterval. Then, by the density of the irrationals in $RR$, there exists some irrational number $p_k in [x_(k-1), x_k]$. By its definition, $t(p_k) = 0$. Since $t(x) >= 0$ for all $x in RR$ and $t(p_k) = 0$, its infimum on this subinterval is 0.

  Since the subinterval was arbitrary, the infimum is zero on all subintervals. Summing them up, we have $L(t,P) = 0$.
]

== (b)

#lemma[
  Let $epsilon > 0$ and define the set of points
  $
    D_(epsilon slash 2) = { x in [0,1]: t(x) >= epsilon slash 2}.
  $

  Then $D_(epsilon slash 2)$ is finite.
]
#proof[
  The set $D_(epsilon slash 2)$ contains all points $x = m slash n$ with $0 <= m <= n$ with $m$ and $n$ co-prime such that $t(x) = 1 slash n >= epsilon slash 2$. (It also contains 0 if $epsilon <= 2$). So
  $
    n <= 2 slash epsilon,
  $
  that is, $n$ is a finite positive integer for any $epsilon$. For each $n$, there are a finite number of possible $m$ (in fact, there are $phi(n)$ such $m$ where $phi$ is the Euler's totient function from elementary number theory, but that's doesn't really matter here). Hence the total number of possible $x = m slash n$ is finite.
]

== (c)

#theorem[
  For any $epsilon > 0$, there is a partition $P_epsilon$ of $[0,1]$ such that $U(t,P_epsilon) < epsilon$. 
]
#proof[

  Let $epsilon > 0$ be given.

  If $epsilon > 2$ then we may pick $P_epsilon = {0,1}$ so $U(t,P_epsilon) = 1 < epsilon$ and the theorem is true.

  Otherwise, $epsilon < 2$ so $D_(epsilon slash 2) != emptyset$ since it contains 0.
  
  By the lemma above there are a finite number, say $N > 0$, points with $t(x) >= epsilon slash 2$. We construct a partition $P_epsilon$ of equal subintervals such that the total length of all subintervals that contain a point in $D_(epsilon slash 2)$ is at most $epsilon slash 2$. Since at most two subintervals can contain a given point (one if it's interior to a subinterval, two if it's at a boundary), we pick the number of subintervals $K$ such that the subinterval length $l=1 slash K$ satisfies
  $
    N dot 2l <= epsilon slash 2 .
  $

  Let $A$ be the total length of subintervals that contain a point in $D_(epsilon slash 2)$. Then $0 < A <= epsilon slash 2$ by construction. Then the sum
  $
    U(t,P_epsilon) = sum_(k=1)^K M_k (x_k - x_(k-1)) = U_1 + U_2
  $
  where $U_1$ is the sum over the subintervals that contain a point in $D_(epsilon slash 2)$, and $U_2$ the sum over those that don't. Then, since $t(x) <= 1$ for all $x$,
  $
    U_1 <= 1 dot A
  $
  while
  $
    U_2 <= epsilon/2 dot (1-A)
  $
  so, since $0 < A <= epsilon slash 2$,
  $
    U_1 + U_2 <= A + epsilon/2 - (A epsilon)/2 <= epsilon/2 + epsilon/2 - (A epsilon)/2 < epsilon .
  $
]

As a consequence, since $L(t,P) = 0$ for any partition of $[0,1]$, $U(t,P_epsilon) - L(t,P_epsilon) < epsilon$ and so $t$ is integrable.

= Problem 2: Examples of integrable functions
Exercise 7.3.5

== (a)

Since the rationals are countable, we may pick some ordering of them. Let $Q_n$ be the set containing the first $n$ rational numbers according to this ordering. Define
$
  f_(n)(x) = cases(
    1 quad & "if" x in Q_n,
    0      & "otherwise" .
  )
$
Then each $f_n$ has a finite number of discontinuities, $f_n -> f$ pointwise where $f$ is Dirichlet's function, and $f$ is not integrable.

== (b)

The question asks for "a sequence $(g_n) -> g$ uniformly where each $g_n$ has at most a finite number of discontinuities and $g$ is not integrable". It doesn't mention boundedness.

Let $g_n: [0,1] -> RR$ be defined as
$
  g_(n)(x) = cases(
    1 slash x quad & "if" x > 0,
    0              & "if" x = 0 .
  )
$

Let $g(x) = g_(1)(x)$. Then $(g_n) -> g$ uniformly since there is no dependence on $n$. Each $g_n$ has one discontinuity, at 0. But since each $g_n$ is unbounded near 0, it is not integrable.

If the $g_n$ were required to be bounded then the request is impossible, since bounded functions with a finite number of discontinuities are integrable, and the uniform limit of integrable functions is integrable.

== (c)

We are asked for a sequence $(h_n) -> h$ uniformly where each $h_n$ is not integrable but $h$ is integrable.

Let $f$ be Dirichlet's function on $[0,1]$ and define
$
  h_(n)(x) = f(x)/n .
$

Then each $h_n$ is not integrable since it is just a scaled version of Dirichlet's function, which is not integrable (scaling by a positive constant $c$ just scales the infimum and supremum on each subinterval, and therefore scales the upper and lower sums, so integrability is invariant under scaling by a constant). But $(h_n)$ converges uniformly to the zero function, which is integrable: given any $epsilon > 0$, pick $N > 1 slash epsilon$ in the definition of uniform convergence.

= Problem 3: Integrability of Dirichlet-like functions
Exercise 7.3.6

Let ${r_1, r_2, r_3, ...}$ be an enumeration of all the rationals in $[0,1]$, and define
$
  g_(n)(x) = cases(
    1 quad & "if" x = r_n,
    0      & "otherwise" .
  )
$

== (a)

Let $G(x) = sum_(n=1)^infinity g_(n)(x)$. Then we claim that $G(x)$ equals Dirichlet's function restricted to $[0,1]$:

If $x in QQ inter [0,1]$ then let $x = r_m$ in the enumeration of the rationals above. Then the $m$'th term in the sum defining $G(x)$ will be 1, and all others will be zero. All partial sums containing $m$ or more terms will therefore be 1. So the sum converges to 1, i.e., $G(r_m)=1$.

If $x in.not QQ$ then each $g_(n)(x) = 0$ so each term in the sum is zero. Therefore every partial sum is zero and the infinite sum converges to 0, i.e., $G(x) = 0$.

So $G(x)$ takes on the same values as Dirichlet's function for all $x in [0,1]$, i.e., they are the same function on $[0,1]$. Since Dirichlet's function is not integrable on $[0,1]$, neither is $G(x)$.

== (b)

Let $F(x) = sum_(n=1)^infinity g_(n)(x) slash n$. The function is well-defined: for every $x$, at most 1 term is nonzero so the series converges. $F(r_n) = 1 slash n$ for rational argument and 0 otherwise.

#lemma[
  $F$ is integrable on $[0,1]$ and
  $
    integral_0^1 F = 0 .
  $
]
#proof[
  Let $epsilon > 0$ be given. Then for any partition $P$, the lower sum $L(F, P) = 0$ because due to the density of irrationals in $RR$, every subinterval contains an irrational point $i$. Then $F(i) = 0$, but $0 <= F(x) <= 1$ for all $x in [0,1]$ so the infimum is 0 on every subinterval.

  Pick any integer $N > 3 slash epsilon$ and let $P_epsilon$ be the partition that subdivides the interval into $N^2$ equal parts. Then the length of each subinterval is $1 slash N^2$ and $1 slash N < epsilon slash 3$.

  Write the upper sum $U(F,P_epsilon) = U_1 + U_2$, where $U_1$ is the contribution from subintervals containing at least one point $r_n$ with $n <= N$, and $U_2$ the contribution from the remaining subintervals.

  Then for all $r_n$ with $n <= N$ we have $F(r_n) = 1 slash n <= 1$. These $N$ points could belong to at most $2N$ subintervals (if they're located at endpoints). Let $A$ be the number of such subintervals, so $A <= 2N$. Since $F(x) <= 1$ for all $x in [0,1]$, the supremum on these subintervals is at most 1. So
  $
    U_1 <= 1 dot A dot 1 slash N^2.
  $

  The remaining $N^2 - A$ subintervals contain no points $r_n$ with $n <= N$, so $F(x) <= 1 slash N < epsilon slash 3$ for points in these subintervals. So the supremum on each subinterval is also bounded by $epsilon slash 3$. So
  $
    U_2 <= epsilon/3 dot (N^2 - A) dot 1 slash N^2 ,
  $
  so
  $
    U(F,P_epsilon) \
    = & U_1 + U_2 \
    <= & A/N^2 + epsilon/3 - (A epsilon)/N^2 \
    < & 2N/N^2 + epsilon/3 \
    = & 2/N + epsilon/3 \
    < & epsilon .
  $

  Hence $U(F,P_epsilon) - L(F,P_epsilon) < epsilon$ so the function is integrable, and the integral is 0 since $L(F,P) = 0$ for any partition.
]

= Problem 4: Integrability of functions that agree on all but a certain set of points
Exercise 7.3.7

Assume $f: [a,b] -> RR$ is integrable.

== (a) 

#lemma[
  If $g$ satisfies $g(x) = f(x)$ for all but one point in $[a,b]$, then $g$ is integrable as well.
]
#proof[
  Since $f$ is integrable on $[a,b]$, there exists a partition $P_epsilon$ of $[a,b]$ with
  $
    U(f,P_epsilon) - L(f,P_epsilon) < epsilon slash 2 .
  $

  Let $p in [a,b]$ be the point where $f$ and $g$ disagree and assume for now that $p in (a,b)$. Since $f$ is bounded and $g$ agrees with $f$ at all points except $p$, $g$ is also bounded and, there exists $M > 0$ satisfying $abs(f(x)) <= M$ and $abs(g(x)) <= M$ for all $x in [a,b]$.
  
  Consider the partition $P = P_epsilon union {p-delta, p+delta}$ where $delta = epsilon slash 16M$. Since $P$ is a refinement of $P_epsilon$,
  $
    U(f,P) - L(f,P) <= U(f,P_epsilon) - L(f,P_epsilon) < epsilon slash 2.
  $

  We are interested in bounding the quantity
  $
    & [U(g,P) - L(g,P)] - [U(f,P) - L(f,P)] \
    = & sum_(k=1)^n (M_(k)^g - m_(k)^g) Delta x_k - sum_(k=1)^n (M_(k)^f - m_(k)^f) Delta x_k .
  $

  It's possible that $P_epsilon$ has points closer to $p$ than these new points, or that $p in P_epsilon$. Regardless, the total width of all subintervals that contain $p$ is at most $2 delta$. Since $f$ and $g$ agree on all subintervals except those containing $p$, all terms in these sums cancel except the ones corresponding to those subintervals. Let $K$ be the set of $k$ indexing those subintervals:
  $
    & [U(g,P) - L(g,P)] - [U(f,P) - L(f,P)] \
    & = sum_(k in K)(M_(k)^g - m_(k)^g - M_(k)^f + m_(k)^f) Delta x_k
  $

  Since $M$ is a common bound for both $f$ and $g$, we have $M_(k)^g - m_(k)^g <= 2M$ and $M_(k)^f - m_(k)^f <= 2M$, so
  $
    & abs([U(g,P) - L(g,P)] - [U(f,P) - L(f,P)]) \
    & <= 4 M dot 2 delta \
    & = epsilon slash 2.
  $

  So, since $a-b <= abs(a-b)$, we have
  $
    U(g,P) - L(g,P) - [U(f,P) - L(f,P)] <= epsilon slash 2
  $
  so
  $
    U(g,P) - L(g,P) <= U(f,P) - L(f,P) + epsilon slash 2 < epsilon 
  $
  and $g$ is integrable.

  If $p$ is an endpoint of $[a,b]$ then substantially the same argument works, except the points added to the partition must be clamped to $[a,b]$ and the resulting subinterval is smaller, which only makes the bound tighter.
]

#theorem[
  If $g$ satisfies $g(x) = f(x)$ for all but a finite number of points in $[a,b]$, then $g$ is integrable as well.
]
#proof[
  Let $S$ be the set of points on which $f$ and $g$ disagree. We proceed by induction on the number of points $N$ in $S$. If $N=0$ then there is nothing to prove, for the two functions are identical.

  Suppose the theorem is true for some $N >= 0$, that is, if $f$ is integrable and $f$ and $g$ agree on all but $N$ points then $g$ is integrable as well.

  Suppose that $f$ integrable and $g$ disagrees with $f$ at $N+1$ points. Let $p$ be one of those points. Let $h$ be the function such that
  $
    h(x) = cases(
      f(x) quad & "if" x = p,
      g(x)      & "otherwise" .
    )
  $
  Then $h$ disagrees with $g$ at that one point $p$, and disagrees with $f$ at $N$ points. By the inductive hypothesis, $h$ is integrable. So by the preceding lemma, $g$ is integrable and the inductive step is complete.
]

== (b)

Let $f$ be the zero function and $g$ be Dirichlet's function. Then $g$ differs from $f$ at a countable number of points: the rationals. $f$ is integrable but $g$ is not integrable.

= Problem 5: Content Zero
Exercise 7.3.9

== (a)

#theorem[
  Let $f$ be a bounded function on $[a,b]$ whose set of discontinuities has content zero. Then $f$ is integrable.
]
#proof[
  Let $epsilon > 0$ be given. We will construct a partition of $P$ of $[a,b]$ with $U(f,P) - L(f,P) < epsilon$.

  Since $f$ is bounded, there exists some $M > 0$ such that $abs(f(x)) < M$ for all $x in [a,b]$.

  Let $A$ be the set of discontinuities of $f$. Since it has content zero, there exists a finite collection of open intervals ${O_1, O_2, ..., O_N}$ that contains $A$ in its union and whose lengths sum to $epsilon slash 4M$ or less. Let ${a_1, b_1, a_2, b_2, ..., a_N, b_N}$ be the set of all endpoints of these open intervals. Then define the partition $P_0 = {a, a_1, b_1, a_2, b_2, ..., a_N, b_N, b}$, i.e. the set of all endpoints plus $a$ and $b$, deduplicated and sorted. This is a finite set.

  For each subinterval of this partition, either its interior is completely disjoint from all the $O_i$, or its interior is completely contained in one or more of the $O_i$. (I had a hard time coming up with a proof of this. Maybe starting with: Suppose some interior point $x$ of some subinterval is contained in some $O_j$. Then we want to show that actually the whole subinterval is contained in $O_j$, because in order to leave $O_j$ we have to cross an endpoint, which necessarily means leaving the subinterval.)
  
  Let $Q$ be the set of subintervals that lies completely inside one of the $O_i$, and $R$ the set of subintervals whose interior is completely disjoint from all $O_i$. Then we claim that $f$ is continuous on every subinterval of $R$, including at the endpoints: let $S$ be some subinterval of $R$. Then its interior is disjoint from all the $O_i$. Suppose that $f$ is discontinuous at one of the endpoints $e$ of $S$. Then $e in O_i$ for at least one of the open sets $O_i$. So a small neighborhood of $e$ is also contained in $O_i$, but that neighborhood must also contain interior points of $S$, a contradiction.

  Let $abs(R)$ denote the number of subintervals in $R$. Since bounded continous functions are integrable, for each subinterval in $R$ there exists a partition $P_k$ with $U(f,P_k) - L(f,P_k) < epsilon slash (2 abs(R))$.

  We construct our final partition as the union of $P_0$ and all $P_k$. This is a finite union of finite sets, so it is finite. We compute $U(f,P) - L(f,P)$ over the subintervals in $Q$ and the subintervals in the $P_k$. Within the subintervals in $Q$, since the function is bounded, we have $M_k - m_k < 2M$, and the total width of all subintervals in $Q$ is bounded by $epsilon slash 4M$ since the total length of the $O_i$ sums to less than or equal to $epsilon slash 4M$, so
  $
    sum_Q (M_k - m_k) < 2M dot epsilon/(4M) = epsilon/2 .
  $

  And summing over all the subintervals in the $P_k$, we have
  $
    sum_(k=1)^(abs(R)) U(f,P_k) - L(f,P_k) < epsilon/(2 abs(R)) dot abs(R) = epsilon/2 .
  $

  Summing the two we have
  $
    U(f,P) - L(f,P) < epsilon/2 + epsilon/2 = epsilon
  $
  as desired.
]

== (b)

#theorem[
  Any finite set has content zero.
]
#proof[
  Let $epsilon > 0$ be given and let $A = {x_1, x_2, ..., x_N}$ be a finite set of points in $RR$. If $N=0$ then the theorem is trivially true since the empty set is the required collection of finite open intervals.

  Otherwise, let
  $
    O = {(x_n-delta,x_n+delta): 1 <= n <= N}
  $
  where
  $
    delta = epsilon/(2N) .
  $

  Then $A subset.eq union O$ since each point is contained in its corresponding interval, and the total length is
  $
    2N dot delta = epsilon
  $
  as required.
]

== (c)

#theorem[
  The Cantor set has content zero.
]
#proof[
  Let $epsilon > 0$ be given and pick $N$ such that
  $
    (2/3)^N < epsilon/2
  $
  which exists since $((2/3)^n) -> 0$. At the $N$'th level of the construction of the Cantor set, there are $2^N$ closed intervals, each of length $1/(3^N)$, such that the entire Cantor set is contained in the union of these intervals. Let these intervals be denoted $[a_k, b_k]$.

  We construct the collection of covering sets as follows: for each closed interval $[a_k, b_k]$ we include the open interval $(a_k - epsilon/(4 dot 2^N), b_k + epsilon/(4 dot 2^N))$. So each closed interval is a subset of its corresponding open interval, so the entire Cantor set is contained in the union of these open intervals.
  
  Their total length is
  $
    2^N dot (1/3^N + epsilon/(2 dot 2^N)) = (2/3)^N + epsilon/2 < epsilon
  $
  by the choice of $N$.
]

== (d)

#theorem[
  Let
  $
    h(x) = cases(
      1 quad & "if" x in C,
      0      & "if" x in.not C 
    )
  $
  where $C$ is the Cantor set. Then $h$ is integrable and its integral is 0.
]
#proof[
  Outside of the Cantor set, $h$ is the continuous constant function 0. All its discontinuities are a subset of $C$, and by part (c), $C$ is a set of content zero, so all discontinuities of $h$ are in a set of content zero. Therefore, by part (a), $h$ is integrable, and the upper integral equals the lower integral.

  But since the Cantor set is nowhere dense, for any partition of $[0,1]$, every subinterval contains points not in $C$. So since $h(x) >= 0$ for all $x in [0,1]$, every lower sum is zero, and the lower integral is zero, and by integrability, the integral is zero.
]


