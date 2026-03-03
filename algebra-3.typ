#set page(numbering: "1")
#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let lemma = thmbox("lemma", "Lemma", base: none)
#let problem = thmbox("problem", "Problem", base: none)
#let theorem = thmbox("theorem", "Theorem", base: none)
#let proof = thmproof("proof", "Proof")
#let proofidea = thmproof("proof idea", "Proof Idea")
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

= Artin 2.3.1
#problem[
  Prove that the additive group $RR^+$ of real numbers is isomorphic to the multiplicative group $P$ of positive reals.
]

#proof[
  We exhibit the isomorphism $f: RR^+ -> P$ given by $f(x) = e^x$. It is a homomorphism since
  $
    e^(x+y) = e^x e^y
  $
  and it is an isomorphism because an inverse $log: P -> RR^+$ exists.
]

= Artin 2.3.11
#problem[
  Prove that the set $"Aut"(G)$ of automorphisms of a group $G$ forms a group, the law of composition being composition of functions.
]
#proof[
  There is an identity element, the identity automorphism that sends each element to itself.

  Function composition is associative: $f(g(h(x)))$ is the same whether we first form the function $f compose g$ and then evaluate it on $h(x)$, or first compute $g(h(x))$ and then feed that to $f$.

  If $f$ and $g$ are automorphisms then $f compose g$ is an automorphism: that it is bijective can be seen by composing their inverses. To see that it is a homomorphism let $a,b in G$ with $f(x) = a$ and $f(y) = b$. Then
  $
    (f compose g)(x y) = f(g(x y)) = f(g(x) g(y)) = f(g(x)) f(g(y)) = (f compose g)(x) (f compose g)(y)
  $
  using that both $f$ and $g$ are homomorphisms.

  Since each automorphism is a bijective map from $G$ to itself, it has an inverse map. To see that it is a homomorphism:
  $
    f(x y) = f(x) f(y) = a b
  $
  and apply $f^(-1)$ on both sides to get
  $
    f^(-1)(a b) = x y = f^(-1)(a) f^(-1)(b) .
  $

  Therefore all group axioms are satisfied and the set of automorphisms of a group $G$ form a group.
]

= Artin 2.3.12
#problem[
  Let $G$ be a group, and let $phi: G -> G$ be the map $phi(x) = x^(-1)$.

  (a) Prove that $phi$ is bijective.

  (b) Prove that $phi$ is an automorphism iff $G$ is abelian.
]

== (a)
$phi$ is its own inverse. Since an inverse exists, the map is bijective.

== (b)
#proof[

  ($arrow.double.l$) Suppose $G$ is abelian. Since it is bijective, we need only check that $phi$ is a homomorphism:
  $
    phi(x y) = (x y)^(-1) = y^(-1) x^(-1) = x^(-1) y^(-1) = phi(x) phi(y) 
  $

  ($arrow.double.r$) Suppose that $phi$ is an automorphism, then it is a homomorphism, so for any $x, y in G$ we may evaluate
  $
       & phi(x^(-1) y^(-1)) = phi(x^(-1)) phi(y^(-1)) \
    => & (x^(-1) y^(-1))^(-1) = (x^(-1))^(-1) (y^(-1))^(-1) \
    => & (y^(-1))^(-1) (x^(-1))^(-1) = x y \
    => & y x = x y
  $
  so the group is abelian.
]

= Artin 2.4.3
#problem[
  Prove that the kernel and image of a homomorphism are subgroups.
]

#proof[
  (Kernel) Let $K$ be the kernel of a homomorphism $phi$ and let $a, b in K$. To prove it a subgroup we must show that inverses are in $K$ and that it's closed under the group law. For the former we see that
  $
       & phi(a a^(-1)) = phi(a) phi(a^(-1)) \
    => & phi(e) = e phi(a^(-1)) \
    => & e = phi(a^(-1))
  $
  showing that $a^(-1) in K$.

  To show that it's closed we do
  $
    phi(a b) = phi(a) phi(b) = e dot e = e
  $
  showing that $a b in K$.

  Also, for any homomorphism, $phi(e) = e$ so $e in K$.

  Therefore $K$ is a subgroup of $G$.

  (Image) Let $I$ be the image of a homomorphism $phi: G -> G'$ and let $c,d in I$. Then there exist $a, b in G$ such that
  $
    phi(a) = c "and" phi(b) = d .
  $

  Now,
  $
    c d = phi(a) phi (b) = phi(a b) in I ,
  $
  that is, $c d in I$ because $c d = phi("something")$.
  
  Also,
  $
    1 = phi(e) = phi(a a^(-1)) = phi(a) phi(a^(-1)) = c phi(a^(-1))
  $
  so, multiplying the first and last expressions in the chain on the left by $c^(-1)$:
  $
    c^(-1) = phi(a^(-1))
  $
  so $c^(-1) in I$ because $c^(-1) = phi("something")$.

  Also, for any homomorphism, $phi(e) = e$ so $e in I$.

  Therefore $I$ is a subgroup.
]
= Artin 2.4.6
#problem[
  Let $f: RR^plus -> CC^times$ be the map $f(x) = e^(i x)$. Prove that $f$ is a homomorphism, and determine its kernel and image.
]

#proof[
  If $a, b in RR^plus$ then
  $
    f(a+b) = e^(i(a+b)) = e^(i a) e^(i b) = f(a) f(b)
  $
  so $f$ is a homomorphism.

  Its kernel is ${2 n pi: n in ZZ}$.

  Its image is the unit circle ${x + i y: x^2 + y^2 = 1}$.
]
= Artin 2.4.11
#problem[
  Let $G,H$ be cyclic groups, generated by elements $x,y$. Determine the condition on the orders $m,n$ of $x$ and $y$ so that the map sending $x^i arrow.squiggly.long y^i$ is a group homomorphism.
]

For the map to be a homomorphism, when
$
  x^i = x^j
$
we need
$
  y^i = y^j .
$

If $n$ is infinite then $m$ must be infinite, for otherwise consider
$
  x^0 x^m = x^0 = e
$
but
$
  y^0 y^m = y^m != e
$
since $n$ is infinite.

If $n$ is finite then either $m$ is infinite (then it is just the map $ZZ -> ZZ slash n ZZ$) or if $m$ is finite then we need
$
  x^i = x^j "iff" m | i - j
  "and"
  y^i = y^j "iff" n | i - j .
$
For the map to be well-defined, every multiple of $m$ must be a multiple of $n$, i.e. $n divides m$.

= Bonus: Artin 2.2.4
#problem[
  Prove that a nonempty subset $H$ of a group $G$ is a subgroup if for all $x,y in H$ the element $x y^(-1)$ is also in $H$.
]
#proof[
  $H$ is nonempty so it contains at least one element $x$, so by the condition, $x x^(-1) = e in H$.

  Having established that $e in H$, we set $x = e$ and take any other element $y in H$ to obtain that $e dot y^(-1) = y^(-1) in H$. So $H$ contains inverses.

  Let $x, y in H$. Then $y^(-1) in H$. Applying the condition to $x$ and $y^(-1)$, we obtain that
  $
    x (y^(-1))^(-1) = x y in H
  $
  so it's closed.

  Therefore $H$ is a subgroup.
]
= Bonus: Artin 2.2.11
#problem[
  Prove that in any group the orders of $a b$ and $b a$ are equal.
]
#proofidea[
  First prove that whenever $(a b)^n = e$ then $(b a)^n = e$ and vice-versa by solving for $b^(-1)$ and regrouping.

  Then use this fact to argue that if $b a$ had smaller order than $n$, it would contradict $n$ being the smallest for $a b$.
]
#proof[
  Let $n$ be any positive integer such that
  $
    (a b)^n = e .
  $
  Then
  $
    (a b)^(n-1) (a b) = e
  $
  so
  $
    b = [(a b)^(n-1) a]^-1 = [a (b a)^(n-1)]^(-1)
  $ <e1>
  where the last equality follows by regrouping terms.

  Let us compute
  $
    (b a)^n = b a (b a)^(n-1) = [a (b a)^(n-1)]^(-1) a (b a)^(n-1) = e 
  $
  where the last step follows by substituting the value of $b$ from @e1.

  So we have proved that whenever $(a b)^n = e$ then $(b a)^n = e$, and the other direction follows by swapping the roles of $a$ and $b$.

  If $(a b)$ has infinite order then $(a b)^n != e$ for any $n in NN$, so by contrapositive $(b a)^n != e$ for any $n in NN$, i.e., $(b a)$ has infinite order.
  
  Let $N$ be the order of $(a b)$, that is, the smallest positive integer such that $(a b)^N = e$. Suppose for the sake of contradiction that for some $M < N$, $(b a)^M = e$. Then $(a b)^M = e$ contradicting the definition of $N$. Therefore $N$ must be the order of $(b a)$ as well.
]
= Bonus: Artin 2.2.12
#problem[
  Describe all groups $G$ which contain no proper subgroup.
]

#theorem[
  If a group $G$ has no proper subgroup it is either trivial or a cyclic group of prime order.
]
#proofidea[
  Consider cyclic groups generated by an element.
]
#proof[
  If $|G| = 1$ then it is the trivial group and contains no proper subgroups.

  Otherwise we have an element $a$ different from the identity. Consider the cyclic group $H$ that it generates. $H$ must be finite, for otherwise it would be isomorphic to $ZZ$ which has proper subgroups. Therefore $H$ can be written as $e, a, a^2, ..., a^(n-1)$ where $n$ is its order. Then $H <= G$ since it contains the identity and is closed under the group law. But $G$ has no proper subgroups so $H = G$, that is, $G$ is cyclic.

  Suppose $n$ is composite. Then $n = q d$ for integers $q, d > 1$. Then
  $
    a^(q d) = e
  $
  so
  $
    (a^q)^d = e
  $
  so consider the cyclic group generated by $a^q$: $e, a^q, a^(2q), ..., a^((d-1)q)$. This cyclic subgroup has $d$ elements, that is, fewer than $n$. So it would be a proper subgroup of $G$, a contradiction.

  Therefore $n$ must be prime.
]
= Bonus: Any two right cosets of a subgroup $H$ in $G$ are either identical or have no elements in common
This is because the cosets of a subgroup $H$ partition the elements of $G$ into equivalence classes.
#proof[
  If $a$ is in the coset $b H$ then
  $
    a = b h "for some" h in H
  $
  but then
  $
    a h^(-1) = b
  $
  and since $H$ is a subgroup, $h^(-1) in H$, so $b in a H$.

  Also $a in a H$ since $e in H$.

  And if $a in b H$ and $b in c H$ then
  $
    a = b h_1 \
    "and" \
    b = c h_2
  $
  so
  $
    a = c h_2 h_1 = c (h_2 h_1) = c h_3
  $
  where $h_3 = h_2 h_1 in H$ since $H$ is a subgroup.

  Therefore the relation $a ~ b$ if $a in b H$ is an equivalence relation, and therefore it partitions the elements of $G$ into equivalence classes. Since equivalence classes are either identical or disjoint, the same is true of cosets.
]
= Bonus: If $K = ker(phi)$ then $phi(a) = phi(b)$ iff the cosets $a K$ and $b K$ are equal
#proof[
  If $a K = b K$ then $a = b k_1$ for some $k_1 in K$. Apply $phi$ on both sides to get
  $
    phi(a) = phi(b) phi(k_1) = phi(b)
  $
  since $k_1$ is in the kernel.

  Conversely if $phi(a) = phi(b)$ then
  $
    phi(a b^(-1)) = phi(a) phi(b^(-1)) = phi(a) phi(b)^(-1) = phi(a) phi(a)^(-1) = e
  $
  showing that $a b^(-1) in K$, i.e., $a = b k_1$ for some $k_1 in K$, so $a in b K$.

  By the previous problem, this shows that the cosets $a K$ and $b K$ are equal.
]
