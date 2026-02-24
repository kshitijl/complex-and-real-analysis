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

= Small changes I felt that I needed to make in order to make the proofs work

In Problem 5 (c) it seemed to me that I needed to assume that the compact set $K$ is nonempty in order to deduce the existence of a supremum of the image.

In Problem 6 I think the linear map $T$ needs to go from $RR^n$ to itself, not $RR^m -> RR^n$ as written, so that $v^* T v$ can be defined.

= Problem 1: Sequentially compact $=>$ closed and bounded

== Proof idea

To prove closed: suppose we have a convergent sequence. By compactness it has a subsequence whose limit is in $K$. Their limits must be the same, so the parent's limit is in $K$. So $K$ is closed.

To prove bounded: show not bounded => a sequence exists with no convergent subsequence. That sequence is: for bigger and bigger discs, take a point outside that disc, which must exist if the set is not bounded. Any subsequence of this sequence is also unbounded and so cannot converge.

== Proof

#lemma[
  Every convergent sequence in $RR^n$ is bounded.
]
#proof[

  (_Idea: Break sequence into finite prefix + a tail that's within $epsilon$ of the limit._)

  Let $(a_k)$ be a sequence converging to some $a in RR^n$. Pick $epsilon = 1$. Then there exists some $K in NN$ such that
  $
    abs(a_k - a) < epsilon 
  $
  whenever $k >= K$. Then
  $
    abs(a_k) < abs(a) + epsilon
  $
  by applying the triangle inequality to $a$ and $a_k - a$:
  $
     abs(a + a_k - a) <= abs(a) + abs(a_k-a) < abs(a) + epsilon .
  $

  Let $M = max({abs(a_k): k < K})$, where we may take the maximum because the set is finite. Then the sequence is bounded by $max(M, abs(a) + 1)$.
]

#theorem[
  If $K subset.eq RR^n$ is sequentially compact, it is both closed and bounded.
]
#proof[
  Let $(a_k)$ be any sequence whose terms are all in $K$, converging to some limit $a in RR^n$. By compactness of $K$, it has a subsequence that converges to some limit $L in K$.

  By the lemma proved in the last problem set (that every subsequence of a convergent sequence converges to the same point) we have $L=a$. So $a in K$ and so $K$ is closed.

  Suppose $K$ is not bounded. Then for every $k in N$, there must exist a point $a_k in K$ such that $abs(a_k) > k$. Let $(a_k)$ be the sequence of these points. Every subsequence $(a_k_i)$ of this sequence is unbounded: given any $M in RR$, take $i = ceil(M)$. Then

  $
    abs(a_k_i) >= k_i >= i >= M .
  $

  By the lemma proved above, there is no convergent subsequence, so $K$ is not compact.
]

= Problem 2: Closed subset of sequentially compact $=>$ sequentially compact

== Proof idea

Just unwind definitions: any sequence in the subset is also a sequence in the enclosing, so it has a convergent subsequence. But the subset is closed, so the limit is in it.

== Proof

#theorem[
  Let $K$ be sequentially compact, and $A subset.eq K$ be closed. Then $A$ is sequentially compact.
]
#proof[
  Let $(a_k)$ be any sequence whose terms are all in $A$. Since $A subset.eq K$, every term $a_k in K$. By compactness of $K$, there is a subsequence $a_k_i$ converging to a limit $L in K$. By closedness of $A$, since $a_k_i in A$, we have $L in A$. So $A$ is sequentially compact.
]

= Problem 3: Bolzano-Weierstrass Theorem: closed and bounded $=>$ sequentially compact

== (a) Bounded closed intervals in $RR$ are sequentially compact

=== Proof idea

Use the concept of a peak term to get a monotone subsequence, then apply the Monotone Convergence Theorem

If the set of peak terms is infinite then they form a monotone subsequence.

Otherwise there's some term $a_i$ after which there are no more peak terms. Then there must exist a bigger term after it, and a bigger one after that, and so on. Because otherwise we'd have another peak term, contradicting the definition of $a_i$. These form a monotone subsequence.

=== Proof

#theorem[
  _(Bolzano-Weierstrass)_ Bounded closed intervals in $RR$ are sequentially compact.
]
#proof[
  Let $K = [a,b]$ be a bounded closed interval in $R$. Let $(x_k)$ be any sequence whose terms are all in $K$.

  First we show that $(x_k)$ has a monotone subsequence. To that end, let a term $x_k$ of the sequence $(x_k)$ be called a _peak term_ if, for each $m >= k$, we have $x_k >= x_m$.

  Suppose there are infinitely many peak terms of $(x_k)$. Then they form a subsequence; call it $(x_k_i)$. By the definition of peak term, whenever $i >= j$ we have $x_k_i <= x_k_j$. Therefore $(x_k_i)$ is non-increasing, therefore monotone.

  Otherwise, if there are not infinitely many peak terms of $(x_k)$, there must be some finite index $L$ (possibly 1) such that for all $j >= L$, $x_j$ is not a peak term. We form the following subsequence: let $x_k_1$ be $x_L$, the first term that is not a peak term. By the definition of peak term, there must exist some index $k_2 > k_1 = L$ such that $x_k_2 > x_k_1$, otherwise $x_k_1$ would be a peak term. Also, by the definition of $L$ as the index after which there are no more peak terms, $x_k_2$ is not a peak term, so there must exist some index $k_3 > k_2$ such that $x_k_3 > x_k_2$. Continuing in this way, we form the subsequence $(x_k_i)$ of increasing terms.

  Either way we have a monotone subsequence $(x_k_i)$. Since it is contained in $K$, it is bounded. By the Monotone Convergence Theorem from the last problem set, it converges to some limit $M in RR$. By Problem 5 in the last problem set, closed intervals in $R$ are closed sets. Therefore $M in K$, proving that $K$ is sequentially compact.
]


== (b) Closed and bounded in $RR^n$ $=>$ sequentially compact

=== Proof idea

To extend Bolzano-Weierstrass to products of intervals in $RR^n$, find a subsequence whose first coordinate converges, then a subsequence of _that_ whose second coordinate converges, and so on. The other obvious strategy -- find a convergent subsequence in each dimension, then combine them -- seems harder to make work, because the subsequences in each dimension might be mis-aligned, and I couldn't think of a way to fix this. My notation and wording for this proof is very clunky and I couldn't figure out an elegant and precise way to say it.

Then, trap the closed and bounded set inside an enclosing rectange and invoke Problem 2.

=== Proof

#lemma[
  Closed rectangles in $RR^n$ are sequentially compact.
]
#proof[
  In Problem 3 of the last problem set we proved that $v_k -> v$ in $RR^n$ iff, for each $i$, $v_k^((i)) -> v^((i))$.

  Let $R subset.eq RR^n$ be a closed rectangle and let $[a_i, b_i]$ denote the interval in $RR$ corresponding to dimension $i$ of $R$.

  Let $(v_k)$ be any sequence whose terms are all in $R$. Then $v_k^((1))$ lies in a closed and bounded interval of $RR$ and therefore has a convergent subsequence $v_(k_j)^((1))$ by Bolzano-Weierstrass. Form the subsequence of $(v_k_j)$ of $(v_k)$ corresponding to the terms $k_j$ of the subsequence converging in the first dimension. This is a subsequence of $(v_k)$ whose first coordinate converges to some limit $v^((1))$ in $[a_1,b_1]$.

  Now we can find a subsequence of _this_ subsequence whose second coordinate converges to some limit in $[a_2,b_2]$. Also, its first coordinate still converges to $v^((1)) in [a_1, b_1]$ because every subsequence of a convergent sequence converges to the same limit. Also, a subsequence of a subsequence of $(v_k)$ is still a subsequence of $(v_k)$. So we have constructed a subsequence of $(v_k)$ whose first two coordinates converge to individual limits, both of which lie in the respective intervals of $R$.

  Proceeding in this manner, after a finite number $n$ of steps, we have a subsequence of $(v_k)$, each of whose coordinates converges to some limit in $[a_i, b_i]$. Therefore it converges to some limit in $R$. So $R$ is sequentially compact.
]

#theorem[
  If $K subset.eq RR^n$ is closed and bounded, then it is sequentially compact.
]
#proof[
  Since $K$ is bounded, for each dimension $i$ there must exist bounds $a_i, b_i$ such that $a_i <= v^((i)) <= b_i$ for all $v in K$, where $v^((i))$ denotes the $i$'th coordinate of $v$. For, if no such bounds existed, then $K$ would contain points of arbitrarily large norm, contradicting the boundedness of $K$. (This is so because for the usual Euclidean norm, $abs(v^((i))) <= abs(v)$).

  Form the closed rectangle $R$ that is the product of $[a_i,b_i]$ in each dimension. By the lemma proved above, $R$ is sequentially compact. By construction $K subset.eq R$. Therefore by Problem 2, since $K$ is a closed subset of a sequentially compact set, $K$ is sequentially compact.
]

= Problem 4: $f$ continuous $<=>$ preimages of closed sets are closed

== Proof ideas

=== Continuous $=>$ preimages of closed sets are closed

Just unwind definitions. A convergent sequence in the preimage of $B$ produces, in the $B$, a convergent sequence, because $f$ is continuous. $B$ is closed, so contains the limit point, so the original limit must then be in the preimage of the set.

=== Preimages of closed sets are closed $=>$ continuous

The main idea is that if $f$ isn't continuous then for some sequence $a_n -> L$, there's a finite bit of room between $f(L)$ and infinitely many of $f(a_n)$. So we can put an open ball around $f(L)$ and take its complement to get a closed set whose preimage isn't closed.

_In many more words (still informal):_

This side is more interesting. Prove the contrapositive: if $f$ is not continuous, then some closed set has a preimage that is not closed.

$f$ not continuous gives a sequence which converges to $L$, whose image doesn't converge to $f(L)$. So infinitely many points of $f(a_n)$ stay at least $epsilon$ away from $L$.

So there's some room where we can squeeze in an open ball.

Informal mental picture: draw an open ball of radius $epsilon$ around $f(L)$. It's open, so its complement is closed, and the complement contains infinitely many points of $f(a_n)$. So its preimage contains infinitely many points of $a_n$ but doesn't contain $L$.

To prove this using the definitions and results we've developed so far, that is, without using open sets or open balls or that their complements are closed, we need a lemma to directly prove that the set of points $>=epsilon$ distance from a fixed point is closed.

We'll also need to use the previously proved fact that any subsequence of a convergent sequence converges to the same limit as the parent. We need this because the set of points whose image under $f$ stays $epsilon$ away from $f(L)$ form a subsequence, and it is the convergence of this subsequence that shows that the preimage is not closed.

== Proof

#lemma[
  Let $a in R^n$ be a fixed point and $d > 0$ a fixed positive real number. Then the set $K = {x in R^n: abs(x-a) >= d}$ is closed.
]
#proof[
  Let $(v_k) in K$ be a sequence converging to some limit $v in R^n$. Suppose $v in.not K$. Then $abs(v-a) < d$. Define $r = abs(v-a)$.

  Pick $epsilon = d-r > 0$. Then by convergence of $(v_k)$, for some $N in NN$, $abs(v_N-v) < d-r$.

  Now apply the triangle inequality to $v_N-v$ and $v-a$:
  $
     & abs(v_N - v + v - a) <= abs(v_N-v) + abs(v-a) \
  => & abs(v_N - a) < epsilon + r = d-r+r = d ,
  $

  a contradiction of $abs(v_N - a) >= d$.
]

#theorem[
  If $A subset.eq RR^m$, then a function $f: A -> RR^n$ is continuous iff the preimage of any closed subset of $RR^n$ is closed in $A$.
]
#proof[
  Suppose $f: A -> RR^n$ is continuous and $B subset.eq RR^n$ is a closed set. Let $C$ denote the preimage of $B$ under $f$. Then let $(c_k)$ be a sequence whose terms are all in $C$ converging to some limit $c in A$. By continuity of $f$, the sequence $b_k := f(c_k)$ converges to $b := f(c)$. Since $C$ is the preimage of all of $B$, $f(C) subset.eq B$: every element of $C$ maps to an element in $B$. So each $b_k in B$. Since $b_k -> b$ and $B$ is closed, $b in B$. But then, since $f(c) = b in B$, we have $c in f^-1(B) = C$, so $C$ is closed in $A$. That proves the easy direction.

  Now suppose that $f: A -> RR^n$ is not continuous. Then there must exist some sequence $a_n -> a$ with $a_n in A$ and $a in A$ for which $f(a_n) arrow.not f(a)$. Then there must exist some $epsilon$ such that for no $K in NN$ do all terms $f(a_k)$ with $k >= K$ come within $epsilon$ of $f(a)$. Then the number of terms at least $epsilon$ away from $f(a)$ must be infinite, for, if there were only finitely many such terms, then we could pick $K$ to be index of the last of them.

  Let $(a_n_i)$ be the sequence such that $f(a_n_i)$ is at least $epsilon$ away from $f(a)$. Then $(a_n_i)$ is a subsequence of $(a_n)$, but $(a_n)$ is a convergent sequence, so by the lemma in the last problem set about subsequences of convergent sequences, $(a_n_i)$ must also converge to $a$.

  Let $K = {x in RR^n: abs(x-f(a)) >= epsilon}$. By the lemma proved above, $K$ is closed. Since all $f(a_n_i) in K$, we have all $a_n_i in f^-1(K)$. But $a in.not f^-1(K)$, because $f(a) in.not K$. So $f^-1(K)$ contains a convergent sequence whose limit is not contained within it. We have found a closed set whose preimage is not closed in $A$.
]

= Problem 5: the continuous image of a compact set is compact; Extreme Value Theorem

== Proof ideas

=== Continuous image of a compact set is compact

Just unwind definitions: if there's a sequence in the image, then there's a corresponding sequence in the domain, which must have a convergent subsequence, whose convergence is preserved by $f$, so the image is compact.

=== Extreme Value Theorem

The image of $K$ under $f$ is a compact subset of the real line, so it's closed and bounded. It contains its supremum. Since it is the image under $f$ of $K$, some point in $K$ must map to it.

== Proofs

=== (a)

#theorem[
  Suppose $K subset.eq RR^m$ is sequentially compact and $f: K -> RR^n$ is continuous. Then the image of $f$ is sequentially compact.
]
#proof[
  Let $B = f(K)$ denote the image of $K$ under $f$. Let $(b_n)$ be a sequence whose terms are all in $B$. Then there must be corresponding points $a_n in K$ such that $f(a_n) = b_n$ for each $n in NN$; these form a sequence. By sequential compactness of $K$, there must be a convergent subsequence $(a_n_i)$ whose limit $a$ is contained in $K$. By continuity of $f$, the subsequence $f(a_n_i)$ converges to $f(a)$. Since $B$ is the image of $K$ and $a in K$, we have $f(a) in B$. We have found a convergent subsequence whose limit is in $B$, so $B$ is sequentially compact.
]

=== (b)

Take $K = RR$, the entire real line. It is closed since any convergent sequence in $RR$ converges to some number in $RR$. Take $f(x) = x$, the identity function. It is a rational function, therefore continuous. Then the image of $K$ under $f$ is $RR$ which is unbounded, therefore by Problem 1, not compact.

=== (c)

#theorem[
  If $K subset.eq RR^m$ is nonempty, closed and bounded and $f: K -> RR$ is continuous, then $f$ achieves its supremum on $K$, that is, there exists some $v in K$ such that $f(v) >= f(w)$ for all $w in K$.
]
#proof[
  By Problem 3, $K$ is compact. By the theorem proved above, the image of $K$ under $f$ is some compact subset $B$ of $RR$. By Problem 1, $B$ is closed and bounded.

  Since $K$ is nonempty, its image is also nonempty. So $B$ is bounded and nonempty, therefore it has a supremum. Call it $M$.

  For every $n in NN$, let $epsilon = frac(1,n)$. By the lemma proved in the last problem set as part of the Monotone Convergence Theorem, for every $epsilon$ there exists an element $a in B$ with $a > M - epsilon$. So for every $n$, form the sequence of these $a_n$. By its very construction (since $a_n <= M = sup(B)$) this sequence converges to $M$, and $B$ is closed, therefore $M in B$. But $B$ is the image under $f$ of $K$, so some element $v in K$ must map to $M$.
]

= Problem 6: quadratic forms $v^* T v$ achieve their supremum on the unit sphere

== Proof idea

$S$ is the preimage of a closed set (the singleton ${1}$) under a continuous function ($v |-> v^* v$), so it is closed. Also, it's bounded. So it's compact. So $v^* T v$, a rational (therefore continuous) function, must attain its supremum on it.

== Proof

#theorem[
  Let $T: RR^m -> RR^m$ be a linear map, and let $S = {v in RR^m: norm(v) = 1}$ be the unit sphere. Then the function $v |-> v^* T v$ achieves its supremum on $S$.
]
#proof[
  The function $v |-> v^* T v$ is a quadratic polynomial in the entries $v_i$ of the vector $v$, therefore rational, therefore continuous.
  
  The condition $norm(v) = 1$ is equivalent to $v^* v = 1$, which is a special case of the above with $T = I$.

  So $S$ is the preimage under a continuous function of the closed set ${1}$ (since all singleton sets are closed), therefore by Problem 4, $S$ is closed in $RR^m$. Also, $S$ is bounded since every element has a norm of 1. Therefore by Problem 3, $S$ is compact.

  Therefore $v |-> v^* T v$, a function from a compact set to the real numbers, must achieve a maximum on $S$.
]

