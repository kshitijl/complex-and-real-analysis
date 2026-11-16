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

= Problem 1: Fundamental group properties
Exercise 2.5 on p. 53.

Let $G$ be a group.

== (a)
#lemma[
  $G$ has exactly one identity element.
]
#proof[
  By the group axioms, $G$ has _at least_ one identity element, say $e$.

  Let $d$ be any identity element. Then
  $
    d &= e dot d && quad #[since $e$ is an identity] \
      &= e       && quad #[since $d$ is an identity]
  $

  So any identity element is equal to $e$. Thus, $G$ has exactly one identity.
]

== (b)

#lemma[
  Let $g,h in G$. Then $(g dot h)^(-1) = h^(-1) dot g^(-1)$.
]
#proof[
  Let $y = (g dot h)^(-1)$. Then
  $
    y dot (g dot h) & = e && quad #[by definition of inverses]\
    (y dot g) dot h & = e && quad #[by associativity]\
    (y dot g) h h^(-1) & = h^(-1) && quad #[multiplying both sides on the right by $h^(-1)$]\
    y dot g & = h^(-1) && quad #[since $h h^(-1) = e$]\
    (y dot g) g^(-1) &= h^(-1) g^(-1) && quad #[multiplying both sides on the right by $g^(-1)$]\
    y (g g^(-1)) &= h^(-1) g^(-1) && quad #[by associativity]\
    y &= h^(-1) g^(-1) && quad #[since $g g^(-1) = e$]
  $
  as desired.
]

== (c)

#lemma[
  Let $g in G$. Then $(g^(-1))^(-1) = g$.
]
#proof[
Let $y=(g^(-1))^(-1)$. Then
  $
    y g^(-1) &= e quad && #[by definition of inverses]\
    (y g^(-1)) g &= e g quad && #[multiplying on the right by $g$]\
    (y g^(-1)) g &= g quad && #[by definition of the identity]\
    y (g^(-1) g) &= g quad && #[by associativity]\
    y e &= g quad && #[by definition of inverses]\
    y &= g quad && #[by definition of the identity]
  $
  as desired.
]

= Problem 2: One-sided axioms are enough
Exercise 2.7 on p. 54.

#theorem[
Let $G$ be a set with a composition law satisfying the following axioms:

(a) (*Right-Identity Axiom*) There is an element $e in G$ so that $g dot e = g$ for all $g in G$.

(b) (*Right-Inverse Axiom*) For all $g in G$ there is an element $h in G$ so that $g dot h = e$.

(c) (*Associative Law*) $g_1 dot (g_2 dot g_3) = (g_1 dot g_2) dot g_3$ for all $g_1, g_2, g_3 in G$.

Then $G$ is a group.
]
#proof[
  Let $g$ be any element of $G$. Then it has a right-inverse $h in G$ satisfying
  $
    g dot h = e .
  $

  Multiply on both sides by $h$ on the left to obtain
  $
    h dot (g dot h) = h dot e .
  $

  By axiom (a), the right hand side above equals $h$, and we may regroup the left hand side by associativity to obtain:
  $
    (h dot g) dot h = h .
  $

  We now multiply both sides on the right by a right-inverse of $h$, call it $f$:
  $
    ((h dot g) dot h) dot f &= h dot f quad && #[multiplying both sides on the right by $f$]\
    (h dot g) dot (h dot f) &= h dot f quad && #[by associativity] \
    (h dot g) dot e &= e quad && #[since $f$ is a right-inverse of $h$] \
    h dot g &= e quad && #[since $e$ is the right-identity]
  $

  Since $g$ was arbitrary, we have shown that a right-inverse of any element is also a left-inverse.

  Now let $e$ be the element from axiom (a) and $g$ be any element of $G$, and $h$ a right-inverse of $g$. Then
  $
    g e &= g (h g) quad && #[since $h$ is also a left-inverse of $g$]\
    g   &= g (h g) quad && #[since $e$ is a right-identity]\
    g   &= (g h) g quad && #[by associativity] \
    g   &= e g     quad && #[since $h$ is a right-inverse of $g$]
  $
  so $e$ is also a left-identity.

  Hence $e$ is a two-sided identity and right-inverses are two-sided inverses, so $G$ satisfies the axioms of a group.
]

= Problem 3: $g^k$ is a generator of a cyclic group iff $gcd(k,abs(G)) = 1$
Exercise 2.10 on p. 55.

#lemma[
  Let $G$ be a finite cyclic group of order $n$, and let $g$ be a generator of $G$. Then $g^n = e$.
]
#proof[
  By definition, $G = {e, g, g^2, ..., g^(n-1)}$ and each power $g^j$ of $g$ is distinct when $0 <= j < n$.

  Suppose $g^n != e$. Then $g^n = g^k$ for some $0 < k < n$. We may cancel $g^k$ from both sides to obtain
  $
    g^(n-k) = e,
  $
  where $0 < n-k < n$. But this contradicts the fact that each power $g^j$ of $g$ is distinct when $0 <= j < n$.
]

#lemma[
  Let $G$ be a finite cyclic group of order $n$, and let $g$ be a generator of $G$. If $g^m = e$ then $m equiv 0 (mod n)$.
]
#proof[
  By the division algorithm,
  $
    m = q n + r
  $
  with $0 <= r < n$. Then
  $
    g^m = (g^n)^q g^r = g^r
  $
  by the lemma above, so
  $
    g^r = e .
  $

  Since $e, g, g^2, ..., g^(n-1)$ are distinct, and $g^0 = e$, we must have $r = 0$ and therefore $m = q n$.
]

#theorem[
  Let $G$ be a finite cyclic group of order $n$, and let $g$ be a generator of $G$. Then $g^k$ is a generator of $G$ iff $gcd(k,n) = 1$.
]
#proof[
  ($arrow.l.double$) Suppose that $gcd(k,n) = 1$. Then there exist integers $a,b$ such that
  $
    a k + b n = 1 .
  $

  Raising $g$ to both sides,
  $
    (g^k)^a dot (g^n)^b = g .
  $
  But $g^n = e$ by the lemma above, so
  $
    (g^k)^a = g .
  $ 

  Consider the set $H = {..., g^(-3k), g^(-2k), g^(-k), e, g^k, g^(2k), g^(3k), ...}$. Since the group $G$ is closed under composition, $H subset.eq G$. And $g in H$ since $g = g^(a k)$. But this means that $g^2 in H$, since $g^2 = (g^k)^(2a)$, and similarly for all higher powers of $g$. Thus, $G subset.eq H$, so $G = H$ and $g^k$ is a generator of $G$.

  ($arrow.r.double$) Suppose that $g^k$ is a generator of $G$. Then every element of $G$ is a power of $g^k$, and $g in G$, so there exists some integer $a$ such that
  $
    g^(a k) = g .
  $

  By cancellation,
  $
    g^(a k - 1) = e 
  $
  so
  $
    a k - 1 equiv 0 (mod n)
  $
  which can be written as
  $
    a k - 1 = b n
  $
  for some integer $b$. Rearranging this gives
  $
    a k - b n = 1 .
  $
  Any common divisor of $n$ and $k$ must divide the left hand side, so it must divide the right hand side as well, so $gcd(n,k) = 1$.
  
]

= Problem 4: subsets of $"GL"_2(RR)$

Exercise 2.16 on p. 57. [Feel free to assume without proof that the determinant is multiplicative, that is, $det(A B)=det(A) det(B)$ for any matrices $A$ and $B$.]

In all parts of this problem, the group law inherits associativity from $"GL"_2(RR)$. And whenever $A,B in G$ then $A B in "GL"_2(RR)$ since $A,B in "GL"_2(RR)$. 
== (a)

$
  G = { mat(a, b; c, d) in "GL"_2(RR) : a d - b c = 2 }
$

This set is not a group. The matrix
$
  A = mat(2, 0;0,1) in G
$

but $det(A^2) = 4$ so $A^2 in.not G$. $G$ is not closed under composition.

== (b)

$
  G = { mat(a, b; c, d) in "GL"_2(RR) : a d - b c in {-1,1} }
$

This set is a group. Let $A in G$.

$A in "GL"_2(RR)$, so $A$ is invertible by definition, and $A^(-1) in "GL"_2(RR)$ as well.

$
  A A^(-1) = I
$
so
$
  det(A) det(A^(-1)) = 1
$
so
$
  det(A^(-1)) = 1/det(A) .
$

Since $det(A) = plus.minus 1$ for $A in G$, $det(A^(-1)) = plus.minus 1$ as well, so $A^(-1) in G$. So $G$ contains inverses.

$G$ is closed under composition: $det(A B) = det(A) det(B) = plus.minus 1$ for $A,B in G$.

And $I in G$ since $det(I) = 1$.

== (c)

$
  G = { mat(a, b; c, d) in "GL"_2(RR) : c = 0 }
$

This set is a group:

$I in G$.

For any $A = mat(a,b;c,d) in G$, its inverse is $(1/det(A)) mat(d, -b; -c,a)$, which is also in $G$ since $-c = 0$.

For any $A, B in G$, the lower left element of the product $A B$ is $c_A a_B + d_A c_B = 0$ since $c_A = 0$ and $c_B = 0$. So $c_(A B) = 0$, so $A B in G$, so $G$ is closed under composition.

== (d)
$
  G = { mat(a, b; c, d) in "GL"_2(RR) : d = 0 }
$

This set is not a group. Let $A = mat(1,1;1,0)$. Then $det(A) != 0$ and $d_A = 0$ so $A in G$, but
$
  A^2 = mat(1,1; 1,0) mat(1,1;1,0) = mat(2,1; 1, 1) in.not G,
$
so $G$ is not closed under composition. (It also doesn't contain an identity.)


== (e)

$
  G = { mat(a, b; c, d) in "GL"_2(RR) : a = d = 1 "and" c = 0 }
$

This set is a group.

Let $A = mat(1,s;0,1) in G$. Then since $A in "GL"_2(RR)$, $A$ is invertible. Its inverse is
$
  (1/det(A)) mat(1, -s; 0, 1) = mat(1,-s;0,1) in G
$
since $det(A) = 1$.

So $G$ contains inverses.

$I in G$, so $G$ contains an identity.

Let $B = mat(1,t; 0, 1) in G$. Then a computation shows that
$
  A B = mat(1, s+t; 0, 1).
$

So $A B in G$, and $G$ is closed under composition.

= Problem 5: The map $phi(g) = g^(-1)$
Exercise 2.21 on p. 58.

Let $G$ be a group, and consider the function
$
  phi: G -> G, quad phi(g) = g^(-1)
$

== (a)
#lemma[
  $phi(phi(g)) = g$ for all $g in G$.
]
#proof[
  $phi(phi(g)) = phi(g^(-1)) = (g^(-1))^(-1) = g$ as proved in problem 1.
]

== (b)
#lemma[
  $phi$ is a bijection.
]
#proof[
  Suppose $phi(a) = phi(b)$ for some $a,b in G$. Then
  $
    a^(-1) = b^(-1) .
  $
  Multiplying on the left by $a$,
  $
    e = a b^(-1) .
  $
  Now multiplying on the right by $b$,
  $
    b = a .
  $
  Thus $phi(a) = phi(b) => a = b$, so $phi$ is injective.

  Now consider some $g in G$. We compute
  $
    phi(g^(-1)) = (g^(-1))^(-1) = g,
  $
  so there exists an element $g^(-1) in G$ which maps to $g$ under $phi$. Thus $phi$ is surjective.

  Hence $phi$ is a bijection.

  (We can also use the fact proved in the previous part: $phi(phi(g)) = g$ means that $phi$ is its own two-sided inverse, and any function with a two-sided inverse is a bijection.)
]

== (c)

#theorem[
  $phi$ is a group homomorphism iff $G$ is abelian.
]
#proof[
  ($=>$) Suppose that $phi$ is a group homomorphism. Then for all $a,b in G$,
  $
    phi(a b) = phi(a) phi(b).
  $
  Applying this to $a^(-1)$ and $b^(-1)$ we get
  $
    (a^(-1) b^(-1))^(-1) = (a^(-1))^(-1) (b^(-1))^(-1)
  $
  which simplifies to
  $
    (b^(-1))^(-1) (a^(-1))^(-1) = a b,
  $
  that is,
  $
    b a = a b .
  $
  So $G$ is abelian.

  ($arrow.l.double$) Suppose that $G$ is abelian. Then for all $a,b in G$,
  $
    a b = b a .
  $
  Applying $phi$ to both sides,
  $
    phi(a b) = phi(b a).
  $
  The right hand side is
  $
    phi(b a) = (b a)^(-1) = a^(-1) b^(-1) = phi(a) phi(b).
  $

  So
  $
    phi(a b) = phi(a) phi(b),
  $
  showing that $phi$ is a group homomorphism.
]

= Problem 6: Isomorphic groups
Exercise 2.23 on p. 58.

Let $G_1$ and $G_2$ be groups, suppose that $phi: G_1 -> G_2$ is an isomorphism.

== (a)
#lemma[
  If $G_1$ is finite then $G_2$ is also finite, and $\# G_1 = \# G_2$.
]
#proof[
  Let $G_1 = {x_1, x_2, ..., x_n}$ where $n = \#G_1$ and the $x_i$ are distinct. Then consider the set
  $
    H = {phi(x_1), phi(x_2), ..., phi(x_n)} .
  $

  Since $phi$ is injective, each element of $H$ is distinct, so $\#H = n$.

  Since the codomain of $phi$ is $G_2$, we have $H subset.eq G_2$. 

  Since $phi$ is surjective, for every element $y in G_2$, there exists some $x in G_1$ such that $y = phi(x)$, so $y in H$. Thus $G_2 subset.eq H$. Putting these together, $G_2 = H$ is finite and $\#G_2 = n = \#G_1$.
]

== (b)
#lemma[
  If $G_1$ is abelian then $G_2$ is abelian.
]
#proof[
  Let $x,y in G_2$. Since $phi$ is surjective, there exist elements $a,b in G_1$ such that $x = phi(a)$ and $y = phi(b)$.

  Since $G_1$ is abelian
  $
    a b = b a,
  $
  and since $phi$ is a group homomorphism,
  $
    phi(a b) = phi(a) phi(b)
  $
  and
  $
    phi(b a) = phi(b) phi(a) .
  $

  Putting these together,
  $
    x y = phi(a) phi(b) = phi(a b) = phi(b a) = phi(b) phi(a) = y x,
  $
  so $G_2$ is abelian.
]

== (c)
#lemma[
  If $a in G_1$ has order $n$, then $phi(a) in G_2$ also has order $n$.
]
#proof[
  By definition, the order of $a$ is the smallest positive $n$ with $a^n = e$.

  Since $phi$ is a group homomorphism,
  $
    phi(a)^n = phi(a^n) = phi(e) = e,
  $
  where the first step follows by induction.

  Now suppose that $phi(a)^k = e$ for some positive $k < n$. Then $phi(a^k) = e$. Since $phi$ is injective and $phi(e) = e$, we must have $a^k = e$, a contradiction of the fact that $n$ is the _smallest_ integer with $a^n = e$.

  Thus $n$ is the smallest positive integer such that $phi(a)^n = e$.
]

== (d)
#lemma[
  Suppose that $G_1$ has $k$ distinct elements of order $n$. Then $G_2$ also has $k$ distinct elements of order $n$.
]
#proof[
  Let $a_1, a_2, ..., a_k in G_1$ be $k$ distinct elements of order $n$. Then by the previous part, every element $a_i$ maps to an element $phi(a_i) in G_2$ of order $n$. Since $phi$ is injective and the $a_i$ are distinct, all the $phi(a_i)$ are also distinct.
]

I'm not sure if this problem is asking for the stronger statement, that if $G_1$ has exactly $k$ distinct elements of order $n$ then so does $G_2$. We can get there easily once we prove that $phi^(-1)$ is also an isomorphism, but I didn't think that's what the book is asking for so I didn't write it up.


= Problem 7: Relationships between cyclic, dihedral, symmetric and quaternion groups
Exercise 2.24 on p. 58.

Let $C_n$ be a cyclic group of order $n$, $D_n$ the $n$th dihedral group, and $S_n$ the $n$th symmetric group.

== (a)
#lemma[
  $C_2$ and $S_2$ are isomorphic.
]
#proof[
  Let $C_2 = {e, g}$ where $g$ is a generator so $g^2 = e$. Let $S_2 = {"id", tau}$ where $"id"$ is the identity permutation and $tau$ swaps the two elements. 

  Let $phi(e) = "id"$ and $phi(g) = tau$. Then $phi$ is bijective since it's a function between two 2-element sits and it hits both elements.

  $phi$ is a homomorphism: for any product involving the identity, $phi$ satisfies the homomorphism condition since it maps identity to identity. Now, $phi(g^2) = phi(g) phi(g)$ since $g^2 = e$ and $tau^2 = "id"$.

  Hence the two sets are isomorphic.
]

== (b)
#lemma[
  $D_3$ is isomorphic to $S_3$.
]
#proof[
  The book defines the dihedral group as the group of valid permutations of the vertices of the $n$-gon. With this definition, $D_3 subset.eq S_3$. So the identity map $phi: D_3 -> S_3$ defined by
  $
    phi(x) = x
  $
  is trivially a homomorphism and injective since both groups use composition of permutations as their group law. And it's bijective because $\# D_3 = 6 = \# S_3$.
]

== (c)
#lemma[
  Let $m >= 3$. For every $n$, the groups $C_m$ and $S_n$ are not isomorphic.
]
#proof[
  If $m != n!$ then the two groups have different orders and are therefore not isomorphic.

  So suppose that $m = n!$. Since $m >= 3$ we must have $n >= 3$ since $1! = 1$ and $2! = 2$.

  The cyclic group $C_m$ is abelian: by definition the composition rule is
  $
    g^i dot g^j = g^(i + j mod m) = g^(j+i mod m) = g^j dot g^i .
  $

  But the symmetric group $S_n$ is not abelian when $n >= 3$. Let $a$ be the permutation that fixes 1, swaps 2 and 3, and fixes all other elements. Let $b$ be the permutation that fixes 3, swaps 1 and 2, and fixes all other elements. Then $(a compose b)(1) = 3$ but $(b compose a)(1) = 2$. The permutations $a$ and $b$ are members of every $S_n$ with $n >= 3$.

  So $C_m$ is abelian but $S_n$ is not. So they are not isomorphic.
]

== (d)
#lemma[
  For every $n >= 4$, the groups $D_n$ and $S_n$ are not isomorphic.
]
#proof[
  The group $D_n$ has $2n$ elements, while $S_n$ has $n!$ elements. For $n >= 4$, $n! > 2n$ (by induction). So the groups are not isomorphic.
]

== (e)
#lemma[
  Let $m >= 4$ and $n >= 4$. Then $D_m$ and $S_n$ are not isomorphic.
]
#proof[
  Let $m = n!/2$, for otherwise the groups cannot be isomorphic because they have different sizes.

  The dihedral group has an element of order $m$ which generates all the rotations. We will show that the symmetric group has no element of order $n!/2$.

  Consider some permutation $sigma$. When we repeatedly apply it to some element $i$ we obtain elements $i, sigma(i), sigma(sigma(i)), ... (sigma^(k_1))(i)$ until we get $i$ again. All elements visited in this chain are also mapped to their starting point after $k_1$ applications of sigma, and there are exactly $k_1$ elements like this in the chain.

  The permutation acts on $n$ total elements. Take one of the $n-k_1$ elements not in the first chain and repeatedly apply $sigma$ to it. We obtain another chain, this time of size $k_2$ and period $k_2$.

  In total we get numbers $k_1, k_2, ..., k_j$ such that $sum k_i = n$. Then the period of $sigma$ is $product k_i$.

  We need to bound this product and show that it's strictly less than $n!/2$. I think there must be a better way, but here's what I came up with.

  By the AM-GM inequality, let $j$ be the number of chains, and we get
  $
    (product k_i)^(1/j) <= n/j
  $
  so
  $
    product k_i <= (n/j)^j .
  $

  Taking logs and derivatives and setting to zero,
  $
    ln(n/j) - 1 = 0
  $
  so
  $
    j = n/e
  $
  so
  $
    product k_i <= e^(n/e) .
  $

  At this point I stared at a graph and observed that
  $
    e^(n/e) < n!/2 
  $
  for $n >= 4$. (I think we can get this by induction as well.)

  #figure(
    image("algebra-2-1.png", width: 100%),
    caption: [graph of $e^(x/e)$ (red) and $x!/2$ (green)],
  )
  
  Therefore $sigma$ can't have a period big enough to match that of the smallest rotation in the dihedral group, so the two groups can't be isomorphic.
]

== (f)
#lemma[
  The cyclic group $C_8$, dihedral group $D_4$ and the quaternion group $Q$ are not isomorphic.
]
#proof[
  $C_8$ has one element of order 2, the middle element $g^4$. It has two elements of order 4, $g^2$ and $g^6$.

  In $D_4$, every flip has order 2, plus the middle rotation $r^2$. So 5 elements of order 2. And two of the rotations have order 4, $r$ and $r^3$. (Where $r$ is the generator of the rotations.)

  In the quaternion group, -1 has order 2, and each of $i,j,k,-i,-j,-k$ have order 4.

  Here's a table:

#table(
  columns: 3,
  [group], [order 2], [order 4],
  [$C_8$], [1], [2],
  [$D_4$], [5], [2],
  [$Q$],   [1], [6],
)

  So none of these can be isomorphic to any of the others.
]

