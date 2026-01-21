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

= Problem 1

I claim that the sequence $(v_k) = 0, 1, 0, 1, ...$, i.e., where
$
  v_k = cases(0 & "if" k "is even",
  1 & "if" k "is odd")
$

is a sequence in $RR^1$ that doesn't converge to anything.

For, suppose that it did converge to some real number $v$. Then we may pick any $epsilon > 0$, and convergence assures that there exists a $K in NN$ (which may depend on $epsilon$) such that for every $k >= K$, $abs(v_k - v) < epsilon$. Let us pick $epsilon = frac(1,3)$. For every $K$, we can find an even $k_e >= K$ and an odd $k_o = k_e + 1 >= K$ such that $v_(k_e) = 0$ and $v_(k_o) = 1$.

Then, we have
$
  abs(0 - v) < epsilon "and" abs(1-v) < epsilon 
$

so

$
  abs(0-v) + abs(1-v) < 2 epsilon = frac(2,3) .
$

But by the triangle inequality, for every $a,b,c in RR$,
$
  abs(a-c) <= abs(a-b) + abs(b-c) .
$


Setting $a=0$ and $c=1$, we have for every $b in RR$,
$
  abs(0-1) = 1 <= abs(0-b) + abs(b-1) .
$

So the triangle inequality requires that the RHS must be greater-than-or-equal to 1 for every $b in RR$, but convergence requires the existence of a $b = v$ for which the RHS is smaller than $frac(2,3)$, a contradiction.

= Problem 2

Let $(v_k)$ be a sequence with $(v_k) -> v$ and $(v_k) -> v'$.

Suppose that $v != v'$. Then $v - v' != 0$, so $abs(v-v') > 0$. Define $delta = abs(v-v')$.

By the triangle inequality, for any $v_k$,
$
  abs(v-v') <= abs(v-v_k) + abs(v_k-v') 
$

so
$
  delta <= abs(v-v_k) + abs(v_k-v') .
$<eq:t21>

Let us pick $epsilon = frac(delta,3)$. Then, because $(v_k) -> v$, there exists a $K_v in NN$ such that for every $k >= K_v$, $abs(v_k-v) < epsilon$. Also, because $(v_k) -> v'$, there exists a $K_(v') in NN$ such that for every $k >= K_(v')$, $abs(v_k-v') < epsilon$. Let $K = max(K_v,K_(v'))$. Then for every $k >= K$ we have both
$
  abs(v_k-v) < epsilon
$
and
$
  abs(v_k-v') < epsilon .
$

Adding the two inequalities,
$
  abs(v_k-v) + abs(v_k-v') < 2 epsilon = frac(2 delta,3) .
$

Comparing this with @eq:t21, we get that
$
  delta <= abs(v-v_k)+abs(v_k-v') < frac(2 delta,3) .
$

Since $delta > 0$ we may divide both sides by $delta$ to arrive at
$
  1 < frac(2,3) ,
$
a contradiction.

= Problem 3

($=>$) Suppose that $v_k -> v$ in $RR^n$. To prove convergence of each $(v^((i))_k)$ to $v^((i))$, we must be able, given an $epsilon > 0$, to produce a $K in NN$ such $abs(v^((i))_k - v^((i))) < epsilon$ whenever $k >= K$.

By convergence of $(v_k)$, given any $epsilon > 0$ (which we here take to be the same $epsilon$ we're trying to bound each coordinate by) there exists a $K in NN$ such that for every $k >= K$,
$
   & abs(v_k - v) < epsilon \
=> & sqrt(sum_(j=1)^n abs(v^((j))_k - v^((j)))^2) < epsilon .
$

Since both sides are non-negative, we may square them to obtain
$
  sum_(j=1)^n abs(v^((j))_k - v^((j)))^2 < epsilon^2 .
$

Since each term is non-negative, we have for each $i$ that its term in this sum is less-than-or-equal to the sum:
$
  abs(v^((i))_k - v^((i)))^2 <= sum_(j=1)^n abs(v^((j))_k - v^((j)))^2 < epsilon^2 
$
so
$
   & abs(v^((i))_k - v^((i)))^2 < epsilon^2 \
=> & abs(v^((i))_k - v^((i))) < epsilon
$

where taking square roots is legitimate because $f(x) = sqrt(x)$ is a strictly increasing function.

(Another way to justify the last step without invoking the $sqrt(dot)$ function: suppose for non-negative $a$ and $b$ that $a^2 > b^2$ but $a <= b$. Then we may square the last inequality to obtain $a^2 <= b^2$, a contradiction. (But if I'm being this pedantic then maybe I ought to justify why we can square inequalities when both sides are non-negative... Some level of pedantry seems appropriate when proving statements like these, so close to the axioms.))

($arrow.l.double$) Suppose that each $v^((i))_k -> v^((i))$. Given $epsilon > 0$, define
$
  epsilon_c = frac(epsilon,sqrt(n)) .
$

Then for each $(v^((i))_k)$ there exists a $K_i$ such that for every $k >= K_i$,
$
  abs(v^((i))_k - v^((i))) < epsilon_c .
$

Let $K = max{K_i: 1 <= i <= n}$; the definition is justified because $n$ is finite. Then the inequality above holds for every $i$ whenever $k >= K$.

Squaring both sides (legitimate because both sides are non-negative) and summing over all $i$, we get
$
  sum_(i=1)^n abs(v^((i))_k - v^((i)))^2 < n epsilon_c^2 .
$

The LHS is $abs(v_k - v)^2$; the RHS is
$
  n frac(epsilon^2,n) = epsilon^2 
$

so the inequality becomes
$
  abs(v_k - v)^2 < epsilon^2
$

and we take square roots to get
$
  abs(v_k - v) < epsilon .
$

= Problem 4: Monotone Convergence Theorem

#lemma[
  If $A$ is a nonempty bounded subset of $RR$, then for any $epsilon > 0$, there is some $a in A$ with $a > sup A - epsilon$.
]
#proof[
  Suppose for some $epsilon > 0$ there were no $a in A$ with $a > sup A - epsilon$. Define $M = sup A - epsilon$. Since no element exceeds $M$, then every element is $<= M$: for all $a in A$ we have $a <= M$. In other words, $M$ is an upper bound of $A$. Also, $M < sup A$ since $epsilon > 0$.

  So $M$ is an upper bound that is less than $sup A$, which contradicts the definition of $sup A$ as the _least_ upper bound of $A$.
]

#theorem[
  Any bounded, monotonic sequence in $RR$ converges.
]
#proof[
  Let $(a_k)$ be any bounded, monotonically increasing sequence in $RR$. Let $A$ be the set ${a_k: k in NN}$. Since the sequence $(a_k)$ is bounded, $A$ is also bounded. Since $A$ contains $a_1$, it is nonempty. Therefore by the least upper bound property of real numbers, $A$ has a supremum.

  Fix any $epsilon > 0$. By the lemma proved above, there is some $a in A$ with $a > sup A - epsilon$. Since the set $A$ consists of all the values in the sequence $(a_k)$, there must be at least one $K in NN$ with $a_K = a$. 

  Since the sequence is monotonically increasing, for every $k >= K$, $a_k >= a_K$. Combining this with the inequality for $a_K$, we obtain
  $
    a_k >= a_K > sup A - epsilon
  $
  so
  $
    a_k > sup A - epsilon .
  $
  Rearranging, we get that
  $
    sup A - a_k < epsilon .
  $

  By the definition of supremum, $sup A >= a_k$, so both sides of the inequality above are non-negative. Thus we may take the absolute value to obtain that whenever $k >= K$,
  $
    abs(sup A - a_k) < epsilon .
  $
  Since the choice of $epsilon$ was arbitrary, this proves that the sequence converges (to $sup A$).

  For a monotonically decreasing sequence $(a_k)$ we may give an analogous proof with infimum in place of supremum. Alternatively, we may consider the sequence $(-a_k)$ which is then monotonically increasing.
]

= Problem 5

== (a)

Let $(x_k)$ be a sequence in $RR$ converging to some $x in RR$, and, for some $M in RR$, we have that each $x_k <= M$.

Suppose that $x > M$. Let $epsilon = x-M > 0$. Then there exists some $K in NN$ such that
$
  abs(x_k - x) < epsilon 
$
whenever $k >= K$. Let $k = K$.

Using a basic identity of $abs(dot)$ in one dimension,
$
  -epsilon < x_k - x < epsilon .
$

(To justify this, we can show it holds for both cases of the absolute value function $f(y) =abs(y)$: when $y>=0$ and when $y<0$.)

Adding $x$ to both sides, we have
$
  x - epsilon < x_k < x + epsilon .
$

We're interested in the first of these inequalities. Substituting our chosen value of $epsilon$, we have
$
   & x - (x-M) < x_k \
=> & M < x_k ,
$

a contradiction, arising from the assumption that $x > M$. So $x <= M$.

== (b)

Let $(x_k)$ be any sequence in $RR$ converging to some $x in RR$ such that $x_k in [a,b]$ for every $k in NN$. That is,
$
  a <= x_k <= b
$
for every $k in NN$. By part (a) and the corresponding statement with the inequality in the other direction, we have that
$
  a <= x <= b .
$

So $x in [a,b]$.

So, for every convergent sequence whose terms are all in $[a,b]$, the limit is also in $[a,b]$. By the definition of closed set, the interval $[a,b]$ is a closed set. Since the choice of interval was arbitrary, the conclusion holds for all closed intervals in $RR$.

== (c)

Let $(x_k)$ be any sequence in $RR^n$ converging to some $x in RR^n$ such that $x_k in R$ where $R$ is a closed rectangle in $RR^n$, the product of closed intervals $[a_1, b_1], ..., [a_n, b_n]$.

By Problem 3, for every $i = 1, ..., n$, the sequence obtained from the $i$'th coordinate $(x^((i))_k)$ of $(x_k)$ converges to $x^((i))$.

By the definition of closed rectangle, if $x_k in R$ then $x^((i))_k in [a_i, b_i]$ for every $i = 1, ..., n$. Therefore, by part (b) above, $x^((i)) in [a_i, b_i]$.

By the definition of closed rectangle, then $x in R$, proving that closed rectangles are closed sets.

= Problem 6

I claim that the interval $(0,1]$, a subset of $RR$, is not closed.

To show this, we need only exhibit one convergent sequence whose terms are all in $(0,1]$ but whose limit is not in $(0,1]$.

Take the sequence $a_k = frac(1,k)$. First we prove that it converges to 0. For any $epsilon > 0$, take $N = ceil(frac(1,epsilon)) + 1$. Then for all $k in NN$ such that $k >= N$ we have
$
   & k >= N = ceil(frac(1,epsilon)) + 1 > frac(1,epsilon) \
=> & k > frac(1,epsilon) \
=> & frac(1,k) < epsilon \
=> & a_k < epsilon \
=> & abs(a_k - 0) < epsilon
$

where in the last step we write $abs(a_k) = a_k$ because $a_k = frac(1,k) > 0$. This shows that $a_k -> 0$.

Also, $0 < frac(1,k) <= 1$ for every $k in NN$, so $a_k in (0,1]$.

But $0 in.not (0,1]$. Therefore $(0,1]$ is not closed.

= Problem 7

== (a)

#lemma[
  Let $(a_k)$ be a sequence that converges to $L$ in $RR$. Then any subsequence of $(a_k)$ is also convergent, and it converges to $L$. 
]
#proof[
  Let $(s_k)$ be a subsequence of $(a_k)$. Then there is a strictly increasing (therefore injective) mapping $f: NN -> NN$ such that
  $
    s_k = a_(f(k)) .
  $

  Fix any real $epsilon > 0$. By convergence of $(a_k)$ to $L$, there exists a $K in NN$ such that $abs(a_k - L) < epsilon$ for every $k >= K$. Let $K'$ be any natural number such that $f(K') >= K$. Such a number exists because $f$ is strictly increasing, hence unbounded.
  
  Then, because $f$ is strictly increasing, for every $k' >= K'$, we have
  $
    f(k') >= f(K') >= K ,
  $
  so that
  $
    abs(a_(f(k')) - L) < epsilon ,
  $
  so
  $
    abs(s_k' - L) < epsilon ,
  $
  proving that $s_k -> L$.
]

Let $U = F union F'$ where $F, F'$ are closed sets. Let $(a_k)$ be any convergent sequence whose terms are all in $U$. Let $L$ be its limit.

Then at least one of $F$ and $F'$ must have an infinite number of terms of $(a_k)$: since $a_k in U$ and $U = F union F'$, each $a_k$ must belong to at least one of $F$ and $F'$. But if both $F$ and $F'$ have only a finite number of terms of $(a_k)$, then the total number of terms would be finite, a contradiction.

Without loss of generality let $F$ be a set that has an infinite number of terms of $(a_k)$. Then define $(f_k)$ to be the subsequence consisting of terms of $(a_k)$ that are in $F$. By the lemma proved above, $f_k -> L$. By the fact that $F$ is a closed set, $L in F$. Therefore $L in U$, proving that $U$ is a closed set.

== (b)

Let $I$ be an indexing set (potentially uncountably infinite) and let $C = {F_i: i in I}$ be a collection of closed sets $F_i$. Define
$
  V = inter.big_(i in I) F_i ,
$
their intersection.

Suppose $(a_k)$ is any convergent sequence whose terms are all in $V$. Let $L$ be its limit. Then, by the definition of set intersection and of $V$, for each $k in NN$ and every $i in I$,
$
  a_k in F_i .
$

So for each $i$, $(a_k)$ is a convergent sequence whose terms are all in $F_i$. Therefore, because each $F_i$ is a closed set, $L in F_i$. Therefore by the definition of $V$, $L in V$, proving that $V$ is a closed set.

== (c)

I think we can find both countable and uncountable counterexamples. In both cases I use the fact proved in Problem 5 (b), that closed intervals in $RR$ are closed sets.

=== Uncountable

This is the obvious case.

Let $r$ be a real number in the half-open interval $(0,1]$. Define $I_r = [r,1]$. Then the collection
$
  C = {I_r: r in (0,1]}
$
is an infinite collection of closed sets. But its union is $(0,1]$ (proved below) which, by Problem 6, is not closed.

#lemma[
  The union of the collection $C$ is $(0,1]$.
]
#proof[
  Define
  $
    U = union.big_(r in (0,1]) I_r ,
  $
  i.e., the union of all sets in the collection $C$.
  
  Let $a in (0,1]$. Then $0 < a <= 1$. The set $I_a = [a,1]$ is in the collection $C$, and $a in I_a$. Therefore $a in U$, showing that $(0,1] subset.eq U$.

  Let $a in U$. Then by the definition of $U$, $a in [r,1]$ for some $r in (0,1]$. Since $[r,1] subset (0,1]$ for every $r in (0,1]$, we have $a in (0,1]$, showing that $U subset.eq (0,1]$.
]

=== Countable

For any $k in NN$ define $I_k = [frac(1,k), 1]$. Then the collection
$
  C = {I_k: k in NN}
$
is an infinite collection of closed sets. But its union is $(0,1]$ (proved below) which, by Problem 6, is not closed.

#lemma[
  The union of the collection $C$ is $(0,1]$.
]
#proof[
  Define
  $
    U = union.big_(k in NN) I_k ,
  $
  i.e., the union of all sets in the collection $C$.

  Let $a in (0,1]$. Then $0 < a <= 1$. Let $k = ceil(frac(1,a)) + 1$. Then
  $
    frac(1,k) < a <= 1
  $

  so $a in [frac(1,k), 1]$, which is in the collection $C$. Therefore $a in U$, showing that $(0,1] subset.eq U$.

  Let $a in U$. Then by the definition of $U$, $a in [frac(1,k), 1]$ for some $k in NN$. Since $[frac(1,k), 1] subset (0,1]$ for every $k in NN$, we have $a in (0,1]$, showing that $U subset.eq (0,1]$.
]
