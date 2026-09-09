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

Exercises are from Joseph Silverman's _Abstract Algebra: An Integrated Approach_, First Edition.

= Problem 1: If $a divides c$ and $b divides c$ then $a b divides gcd(a,b) c$
Exercise 1.28 on p. 32.

== (a)

#theorem[
  Let $a,b,c in ZZ$ and suppose that $a divides c$ and $b divides c$ and $gcd(a,b) = 1$. Then $a b divides c$.
]
#proof[
  Since $gcd(a,b) = 1$ there exist $u, v in ZZ$ such that
  $
    a u + b v = 1 .
  $

  Also, by the hypotheses, there exist $m,n in ZZ$ such that
  $
    c = a m quad "and" quad c = b n .
  $

  Now consider the quantity
  $
    a b (n u + m v) = & a b n u + a b m v \
    = & a u (b n) + b v (a m) \
    = & a u dot c + b v dot c \
    = & c (a u + b v) \
    = & c . 
  $
  That is,
  $
    c = a b (n u + m v) = a b ("some integer"),
  $
  proving that $a b divides c$.
]

== (b)
#theorem[
  Let $a, b, c in ZZ$ and suppose that $a divides c$ and $b divides c$. Then $a b divides gcd(a,b) c$.
]
#proof[
  Let $k = gcd(a,b)$. Then there exist $u,v in ZZ$ such that
  $
    a u + b v = k.
  $
  By the hypotheses, there exist $m, n in ZZ$ such that
  $
    c = a m quad "and" quad c = b n .
  $
  Now write
  $
    c k \
    = & c (a u + b v) \
    = & c a u + c b v \
    = & (b n) (a u) + (a m)(b v) \
    = & (a b)(n u) + (a b)(m v) \
    = & a b (n u + m v) \
    = & a b ("some integer"),
  $
  proving that $a b divides c k$.
]
= Problem 2: Every natural number is either 1, a prime or a product of primes
Exercise 1.30 on p. 32.

#lemma[
  If $k in NN$ and $k divides n$ then $k <= n$.
]
#proof[
  By the definition of divisibility, there exists some $m in NN$ such that
  $
    n = k m .
  $
  Since $m >= 1$, and because multiplication by a positive number preserves inequalities, $n = k m >= k$.
]

#theorem[
  If $n in NN$ and $n >= 2$ then there are primes $p_1, p_2, ..., p_r$ such that $n = p_1 p_2 dots.c p_r$.
]
#proof[
  We proceed by induction on $n$. If $n = 2$ then the statement is true since $n = p_1 = 2$ is the required decomposition.

  Now suppose that the statement is true for all $N in NN$ with $1 < N < n$. If $n$ itself is prime then we are done. Otherwise since $n$ is not prime, by definition there must exist some natural $k != 1, k != n$ such that $k divides n$. So
  $
    n = k dot m
  $
  and, by the lemma above, $1 < k < n$ and $1 < m < n$. Then by the inductive hypothesis both $k$ and $m$ can be written as the product of primes, so
  $
    n = k dot m = p_(k_1) p_(k_2) dots.c p_(k_r) dot p_(m_1) p_(m_2) dots.c p_(m_s)
  $
  where $p_(k_i)$ and $p_(m_i)$ are the primes that $k$ and $m$ are respectively the products of.
]

= Problem 3: Generalization of $p divides a b => p divides a "or" p divides b$
Exercise 1.31 on p. 32.

#theorem[
  Let $a_1, ..., a_n in ZZ$, and let $p in NN$ be a prime with the property that $p divides a_1 a_2 dots.c a_n$. Then there is some $1 <= i <= n$ such that $p divides a_i$.
]
#proof[
  We proceed by induction on $n$. If $n = 1$ then the theorem is trivial because then, $p divides a_1$.

  Now assume that the desired statement is true for $N = n-1$ and write
  $
    a_1 a_2 dots.c a_(n-1) a_n = (a_1 a_2 dots.c a_(n-1)) a_n .
  $
  Then, since $p$ divides the LHS, by Proposition 1.35 $p divides a_n$ or $p divides a_1 a_2 dots.c a_(n-1)$. If $p divides a_n$ then the desired statement is true with $i = n$. Otherwise, by the inductive hypothesis, there exists some $1 <= i <= n-1$ such that $p divides a_i$. Either way, the statement is true.
]

= Problem 4: Prime factorizations are unique
Exercise 1.32 on p. 32.

#theorem[
  Let $p_1, ..., p_m in NN$ be primes and let $q_1, ..., q_n in NN$ also be primes. Suppose that their products are equal,
  $
    p_1 p_2 dots.c p_m = q_1 q_2 dots.c q_n .
  $

  Then $m = n$ and after rearranging the factors, $p_i = q_i$ for every $1 <= i <= n$.
]
#proof[
  Since $p_1 divides p_1 p_2 dots.c p_m$, it must be that $p_1 divides q_1 q_2 dots.c q_n$. By Problem 3, there must be some $1 <= i <= n$ such that $p_1 divides q_i$. Since $q_i$ is prime and $p_1 != 1$, it must be that $p_1 = q_i$.

  Without loss of generality, let us reorder the $q$'s so that $i=1$.

  Now we may divide both sides of
  $
    p_1 p_2 dots.c p_m = q_1 q_2 dots.c q_n 
  $
  by $p_1$ to obtain
  
  $
    p_2 p_3 dots.c p_m = q_2 q_3 dots.c q_n .
  $
  By the same argument as above, we find that there must be some $2 <= j <= n$ such that $p_2 = q_j$, and we can again reorder so that $j=2$.
  
  At each stage in this process, the number of factors in each side goes down by 1.

  Suppose that at some stage in this process, there is exactly one factor remaining on the left hand side. Then, after dividing by it on both sides, the LHS must equal 1. Therefore the RHS must also then equal one. Therefore, before that division, the RHS must also have had exactly one factor.

  Suppose that at some stage in this process, there is exactly one factor remaining on the right hand side. Then, by flipping the two sides, we are in the same position as the previous paragraph. So the two sides must have an equal number of factors at every stage in the process, i.e., $m=n$.

  Proceeding in this way, we find that $p_k = q_k$ for every $1 <= k <= n$ and that the process stops when both sides of the equation have no factors left, i.e., the equation is reduced to $1=1$.
]

= Problem 5: $ZZ[sqrt(-5)]$

The set
$
  ZZ[sqrt(-5)] = {a + b sqrt(-5): a, b in ZZ}
$
and
$
  N(a + b sqrt(-5)) = (a + b sqrt(-5)) (a - b sqrt(-5)) = a^2 + 5 b^2
$

== (a)

#theorem[
  $
    N(x y) = N(x)N(y)
  $
]
#proof[
  Let
  $
    x = a_1 + b_1 sqrt(-5) quad "and" quad y = a_2 + b_2 sqrt(-5)
  $
  so
  $
    x y = (a_1 a_2 - 5 b_1 b_2) + (a_1 b_2 + a_2 b_1) sqrt(-5) .
  $
  Let
  $
    p = a_1 a_2 - 5 b_1 b_2 quad "and" quad q = a_1 b_2 + a_2 b_1
  $
  so
  $
    N(x y) = (p + q sqrt(-5))(p - q sqrt(-5)) .
  $

  On the other hand,
  $
    N(x)N(y) = &(a_1 + b_1 sqrt(-5))(a_1 - b_1 sqrt(-5))(a_2 + b_2 sqrt(-5))(a_2 - b_2 sqrt(-5)) \
    = & [(a_1 + b_1 sqrt(-5))(a_2 + b_2 sqrt(-5))][(a_1 - b_1 sqrt(-5))(a_2 - b_2 sqrt(-5))] \
    = & [a_1 a_2 - 5 b_1 b_2 + (a_1 b_2 + a_2 b_1)sqrt(-5)][a_1 a_2 - 5 b_1 b_2 - (a_1 b_2 + a_2 b_1)sqrt(-5)] \
    = & (p + q sqrt(-5))(p - q sqrt(-5)) \
    = & N(x y).
  $
]

== (b)

An element $x in ZZ[sqrt(-5)]$ is said to be irreducible if the only ways to write $x = p q$ with $p, q in ZZ[sqrt(-5)]$ are when one of $p$ or $q$ is $plus.minus 1$.

#lemma[
  If $x in ZZ[sqrt(-5)]$ then $N(x) in ZZ$ and $N(x) >= 0$.
]
#proof[
  If $x in ZZ[sqrt(-5)]$ then there must exist $a,b in ZZ$ such that $x = a + b sqrt(-5)$. Then $N(x) = a^2 + 5b^2 in ZZ$ since $ZZ$ is closed under addition and multiplication. Also, $a^2 >= 0$ and $b^2 >= 0$ so $N(x) >= 0$.
]

#lemma[
  If $x in ZZ[sqrt(-5)]$ and $N(x) = 1$ then $x = plus.minus 1$.
]
#proof[
  If $x in ZZ[sqrt(-5)]$ then there must exist $a,b in ZZ$ such that $x = a + b sqrt(-5)$. Then
  $
    N(x) = 1 = a^2 + 5b^2 .
  $
  Now, if $abs(b) >= 1$ then $a^2 + 5b^2 >= 5 > 1$, which contradicts the equality above. So $b = 0$ (since both $a,b in ZZ$).
  So
  $
    a^2 = 1
  $
  and therefore
  $
    x = a = plus.minus 1 .
  $
]

#theorem[
  $3 + 2 sqrt(-5)$ is irreducible.
]
#proof[
  $N(3 + 2 sqrt(-5)) = 9 + 5 dot 4 = 29$, so if $x = p q$ then $N(p) N(q) = N(x) = 29$. But by the first lemma above, $N(p)$ and $N(q)$ are non-negative integers, while 29 is prime, so without loss of generality we must have
  $
    N(p) = 1 quad "and" quad N(q) = 29 .
  $
  Therefore by the second lemma above,
  $
    p = plus.minus 1
  $
  and so $3 + 2 sqrt(-5)$ is irreducible.
]

#theorem[
  2 is irreducible.
]
#proof[
  $N(2) = 4$ so if $x = p q$ then $N(p) N(q) = N(x) = 4$. But by the first lemma above, $N(p)$ and $N(q)$ are non-negative integers. By factorizing $4 = 2 dot 2$ we see that the possibilities are
  $
    N(p) = 2, N(q) = 2 \
    "or" \
    N(p) = 1, N(q) = 4
  $
  (leaving aside the symmetric case with $N(p) = 4$ and $N(q)=1$).

  If $N(p) = 2$ then there must exist $a,b in ZZ$ such that
  $
    a^2 + 5 b^2 = 2 .
  $
  If $abs(b) >= 1$ then $a^2 + 5b^2 >= 5 > 2$, so $b = 0$. But then it must be that $a^2 = 2$ which is impossible since 2 is irrational.

  Therefore it must be that $N(p) = 1$, so that by the second lemma above, $p = plus.minus 1$ and 2 is irreducible.
]

#theorem[
  29 is not irreducible.
]
#proof[
  $
    (3 + 2 sqrt(-5))(3 - 2 sqrt(-5)) = 29 .
  $
]

== (c)

#theorem[
  ZZ[sqrt(-5)] does not have unique factorization.
]
#proof[
  We previously showed that 2 is irreducible. By a similar argument, by analyzing $a^2 + 5b^2 = 3$, we find that 3 is irreducible.

  Now we show that $x = 1 + sqrt(-5)$ is irreducible:
  $
    N(x) = 6
  $
  so if $x = p q$ then $N(p) N(q) = 6$. If $N(p) = 2, N(q) = 3$ then we must have an integer solution to $a^2 + 5b^2 = 2$, which we have previously shown to be impossible. But then the only remaining factorizations of 6 are $N(p) = 1, N(q) = 6$ or vice-versa. So $x$ is irreducible.

  By essentially the same argument, $1 - sqrt(-5)$ is irreducible.

  Finally:
  $
    (1 + sqrt(-5))(1 - sqrt(-5)) = 2 dot 3 = 6 .
  $
]
