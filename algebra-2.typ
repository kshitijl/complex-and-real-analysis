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

=== (a)
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

=== (b)

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

=== (c)

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

= Problem 3
Exercise 2.10 on p. 55.

= Problem 4
Exercise 2.16 on p. 57. [Feel free to assume without proof that the determinant is multiplicative, that is, {\rm det}(AB)={\rm det} A\cdot {\rm det} B for any matrices A and B.]

= Problem 5
Exercise 2.21 on p. 58.

= Problem 6
Exercise 2.23 on p. 58.

= Problem 7
Exercise 2.24 on p. 58.


