#set page(numbering: "1")
#import "@preview/ctheorems:1.1.3": *
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

= Problem 1: Subsets of disjoint open sets are separated
(Exercise 3.4.5)

== Proof idea

This proof follows just from messing around a little with complements, and remembering that the closure of a set is the smallest closed set that contains it. The sets $A$ and $B$ are a bit of a distraction; what's really going on is that $U$ and $V$ are separated.

In my informal mental picture, there's a bit of "space" between $U$ and $V$. Also, I imagined $U = (-infinity, 0)$ and $V = (0, infinity)$, like in the proof that all connected sets in $RR$ are intervals.

== Proof

#theorem[
  Let $A$ and $B$ be nonempty subsets of $RR$. Let $U$ and $V$ be disjoint open sets with $A subset.eq U$ and $B subset.eq V$. Then $A$ and $B$ are separated.
]
#proof[
  Since $U$ is open and disjoint from $V$, $U^C$ is closed and contains $V$, so it contains $B$ as well. Since $overline(B)$ is the smallest closed set that contains $B$, we have $overline(B) subset.eq U^C$. Consequently, $U inter overline(B) = emptyset$. But $A subset.eq U$, so $A inter overline(B) = emptyset$ as well.

  By an exactly symmetric argument, $overline(A) inter B = emptyset$. Since $A$ and $B$ are given nonempty, these intersections show that they are separated.
]

= Problem 2: Connected $<=>$ in every partition into two sets, one contains a limit point of the other
(Exercise 3.4.6)

== Proof idea

Just unwind definitions.

== Proof

#theorem[
  A set $E subset.eq RR$ is connected if and only if, for all nonempty disjoint sets $A$ and $B$ satisfying $E = A union B$, there always exists a convergent sequence $(x_n) -> x$ with $(x_n)$ contained in one of $A$ and $B$, and $x$ an element of the other.
]
#proof[

  ($=>$) 

  Suppose $E$ is connected. Then it is not disconnected. So for all nonempty disjoint sets $A$ and $B$ satisfying $E = A union B$, they are not separated. So one of $overline(A) inter B$ and $A inter overline(B)$ is nonempty. Without loss of generality, suppose that $overline(A) inter B$ is nonempty. Let $A'$ denote the set of limit points of $A$. Since $A inter B = emptyset$ and $overline(A) = A union A'$, it must be that $A' inter B$ is nonempty. That is, a limit point $x$ of $A$ falls in $B$. Since $x$ is a limit point of $A$, there is a sequence $(x_n)$ whose terms lie in $A$ and $(x_n) -> x$, with $x in B$.

  ($arrow.double.l$)

  We will prove the contrapositive. Suppose $E$ is disconnected. Then it may be written as $E = A union B$, where $A$ and $B$ are nonempty, and $overline(A) inter B = emptyset$ and $A inter overline(B) = emptyset$. Then $A$ and $B$ must be disjoint, otherwise the closure of one would have nonempty intersection with the other.

  Suppose for the sake of contradiction that a sequence $(x_n)$ whose terms are all in $A$ converged to a point $x$ in $B$. Then, since $(x_n) -> x$ and $x_n in A$ but $x in.not A$, the point $x$ is a limit point of $A$, so $x in overline(A)$, contradicting that $A$ and $B$ are separated. So no such sequence exists.

  An exactly symmetric argument shows that no sequence in $B$ can converge to a point in $A$.

  We have proved that $E$ disconnected $=>$ there exist nonempty disjoint $A$ and $B$ where no sequence in one converges to a point in the other. This is the required contrapositive.
]

= Problem 3: $QQ$ is totally disconnected, and so are the irrationals
(Exercise 3.4.7)

== Proof idea

Given two rational numbers, find a multiple of $sqrt(2)$ between them. Then use the construction in the proof that all connected subsets of $RR$ are intervals: two open intervals with a shared endpoint.

To find the point between them, note that $1 < sqrt(2) < 2$ and find an affine mapping that sends 1 to $a$ and 2 to $b$, then take whatever it sends $sqrt(2)$ to.

For the irrationals, the density of $QQ$ in $RR$ hands us a rational directly.

== Proof

== (a)

#theorem[
  $QQ$ is totally disconnected.
]
#proof[
  Let $x, y in QQ$ be any two distinct rational numbers. Without loss of generality let $x < y$ and let
  $
    c = y(sqrt(2) - 1) - x(sqrt(2) - 2) .
  $

  Then $c$ is irrational, for otherwise
  $
    frac(c - 2x + y, y-x) eq.triple sqrt(2)
  $
  would be an algebraic combination of rational numbers and therefore rational (here we use that the field $QQ$ is closed under the usual operations of addition, subtraction, multiplication and division by a nonzero rational).

  We claim that $c > x$ and $c < y$, for
  $
    c - x = (y-x)(sqrt(2) - 1) > 0
  $
  and
  $
    c - y = (y-x)(sqrt(2) - 2) < 0 .
  $

  Let $A = (-infinity, c) inter QQ$ and $B = (c, infinity) inter QQ$. Then
  $
    A union B = ((-infinity, c) union (c, infinity)) inter QQ = (R backslash {c}) inter QQ = QQ
  $
  and $x in A$ and $y in B$.

  But by the Order Limit Theorem, all limit points of $A$ are contained in $(-infinity, c]$, and all limit points of $B$ are contained in $[c, infinity)$. So $overline(A) subset.eq (-infinity, c]$ while $B subset.eq (c, infinity)$ so $overline(A) inter B = emptyset$ and, symmetrically, $A inter overline(B) = emptyset$. Therefore $A$ and $B$ are separated. Since $x$ and $y$ were arbitrary, we have proved $QQ$ to be totally disconnected.
]

#remark[
  We don't really need the explicit construction. We could have said, By density of $QQ$ in $RR$, there's a nonzero rational $d$ between $x/sqrt(2)$ and $y/sqrt(2)$. Then set $c = sqrt(2) d$.
]

== (b)
#theorem[
  The set of irrational numbers is totally disconnected.
]
#proof[
  Let $x,y in RR backslash QQ$ be any two distinct irrational numbers. Without loss of generality let $x < y$. Since they are real and by the density of $QQ$ in $RR$, there exists a $q in QQ$ such that $x < q < y$.

  Let $A = (-infinity, q) inter (RR backslash QQ)$ and $B = (q, infinity) inter (RR backslash QQ)$. Then
  $
    A union B = ((-infinity, q) union (q, infinity)) inter (RR backslash QQ) = (RR backslash {q}) inter (RR backslash QQ) = RR backslash QQ
  $
  and $x in A$ and $y in B$.

  By the same finishing argument as in part (a), $A$ and $B$ are separated and so the irrationals are totally disconnected.
]

= Problem 4: Connected components

== (a)
=== Proof idea
If the union is disconnected then we get separated sets $A$ and $B$ which we can intersect with each member of the collection. This forces each member to live in exactly one of $A$ or $B$. Both must contain at least _one_ member each in order to be nonempty. But that leaves nowhere for $x$ to go.

=== Proof
#theorem[
  Let $scr(S)$ be a collection of connected sets and suppose that there is a point $x$ which is in every set in $scr(S)$. Then $union.big scr(S)$ is connected.
]
#proof[
  Let $S_alpha$ denote a member of $scr(S)$ and
  $
    U = union.big S_alpha
  $
  and $x$ some point such that $x in S_alpha$ for every $S_alpha in scr(S)$. 

  Suppose for the sake of contradiction that $U$ is disconnected. Then $U = A union B$ where $A$ and $B$ are nonempty and separated. So $x$ must be in exactly one of $A$ or $B$. Without loss of generality, let $x in A$.

  For every $S_alpha in scr(S)$ write
  $
    S_alpha = S_alpha inter U = (S_alpha inter A) union (S_alpha inter B) = A_alpha union B_alpha
  $
  where
  $
    A_alpha = S_alpha inter A \
    "and" \
    B_alpha = S_alpha inter B .
  $

  Since $overline(A) inter B = emptyset$, and $overline(A) = A union A'$ where $A'$ is the set of limit points of $A$, and $A'_alpha subset.eq A'$, we see that
  $
    overline(A_alpha) subset.eq overline(A) ,
  $
  so
  $
    overline(A_alpha) inter B = emptyset ,
  $
  so
  $
    overline(A_alpha) inter B_alpha = emptyset .
  $

  By a symmetric argument,
  $
    A_alpha inter overline(B_alpha) = emptyset .
  $

  But each $S_alpha$ is connected, so one of $A_alpha$ and $B_alpha$ must be empty, and $S_alpha = A_alpha$ or $S_alpha = B_alpha$, which means $S_alpha$ is entirely contained within one of $A$ or $B$.

  If any $S_alpha subset.eq B$, then $x in.not S_alpha$ since $x in A$, a contradiction. But if every $S_alpha subset.eq A$ then $B$ is empty, a contradiction.
]

== (b)
#theorem[
  Let $A subset.eq RR$ and for $x, y in A$ define the relation $~$ by declaring that $x ~ y$ if there is a connected set $C subset.eq A$ containing both $x$ and $y$. Then this is an equivalence relation.
]
#proof[
  Reflexive: $x ~ x$ since the singleton set ${x}$ is connected: it cannot be written as the union of two separated sets because it cannot be written as the union of two nonempty sets at all.

  Symmetric: if $x ~ y$ then there is a connected set $C subset.eq A$ containing both $x$ and $y$, so $y ~ x$.

  Transitive: if $x ~ y$ and $y ~ z$ then there are connected sets $C subset.eq A$ and $D subset.eq A$, where $x,y in C$ and $y,z in D$. Notice that $y$ is in both $C$ and $D$, so we may apply the theorem in part (a) to the collection ${C,D}$ to obtain that $C union D$ is connected. Now, $x,z in C union D$ and $C union D subset.eq A$ so $x ~ z$.
]

The equivalence classes with respect to this relation are called the *connected components* of $A$.

== (c)
#theorem[
  If $C$ is the connected component of some $a in A$, then $C$ is the largest connected subset of $A$ containing $a$ (so in particular $C$ is connected), and there exists a closed set $C' subset.eq RR$ such that $C = C' inter A$ (that is, $C$ is "closed in $A$").
]
#proof[
  Let $B subset.eq A$ be connected subset of $A$ such that $a in B$. Let $y in B$ be any point of $B$. Then, since the connected set $B$ contains both $a$ and $y$, we have $a ~ y$. But because $C$ is defined to be the equivalence class of $a$ with respect to $~$, we have $y in C$. Therefore $B subset.eq C$.

  Now suppose for the sake of contradiction that $C$ is disconnected. Then $C = C_1 union C_2$ where $C_1$ and $C_2$ are nonempty separated sets. Let $x in C_1$ and $y in C_2$. Then, since $C$ is defined as an equivalence class of $~$, we have $x ~ y$, so some connected $D subset.eq A$ contains both $x$ and $y$. We proved above that $D subset.eq C$. Define
  $
    D_1 eq.triple D inter C_1 \
    "and" \
    D_2 eq.triple D inter C_2 
  $
  whereby $x in D_1$ and $y in D_2$ so they are nonempty.
  
  Since $D subset.eq C$ we may write
  $
    D = D inter C = D inter (C_1 union C_2) = D_1 union D_2 .
  $
  But since $overline(C_1) inter C_2 = emptyset$, we have $overline(D_1) inter D_2 = emptyset$, and similarly $D_1 inter overline(D_2) = emptyset$, making $D$ disconnected, a contradiction. Therefore $C$ is connected.

  Now we find a closed set $C' subset.eq RR$ such that $C = C' inter A$. Take $C' = overline(C)$. It is clear that $C subset.eq overline(C) inter A$. We claim that $overline(C) inter A subset.eq C$:

  Let $x in overline(C) inter A$. If $x in C$ then we are done. Otherwise $x in L inter A$ where $L$ is the set of limit points of $C$. We claim that $C union {x}$ is connected. Suppose for the sake of contradiction that it is not. Then $C union {x} = E union F$ where $E$ and $F$ are nonempty and separated. Since $C$ itself is connected, all of it must lie entirely within one of $E$ or $F$ (otherwise, $C inter E$ and $C inter F$ would be nonempty and separated, showing $C$ to be disconnected.) Without loss of generality let $C subset.eq E$. Then $F = {x}$ is the only way for $F$ to be nonempty. But now, $overline(C) inter F = {x} != emptyset$ since $x in overline(C)$. Therefore $overline(E) inter F != emptyset$. So $C union {x}$ is connected.

  But $C union {x} subset.eq A$, so as a connected subset of $A$ containing points of $C$, it must be a subset of $C$, as proved above. So $x in C$, and therefore $overline(C) inter A subset.eq C$. We have shown both set inclusions and so conclude that
  $
    C = overline(C) inter A .
  $
]

In response to Nic's email, here's a simpler proof that $C$ is connected:

#theorem[
  $C$ is connected.
]
#proof[
  $C$ is the equivalence class of $a$, so $a in C$. And for every $x in C$ we have $x ~ a$, so there exists some connected set $D_x subset.eq A$ that contains both $x$ and $a$. By the argument before (that every connected subset of $A$ that contains $a$ is a subset of $C$), $D_x subset.eq C$. Therefore
  $
    C = union.big_(x in C) D_x
  $
  where $a in D_x$ for each $D_x$ containing an $x in C$. By the previous result, $C$ is connected.
]

And a simpler proof that $overline(C) inter A = C$:

#lemma[
  Let $X$ be any connected subset of $A$. Then $overline(X) inter A$ is connected.
]
#proof[
  Write $Y = overline(X) inter A = X union (X' inter A)$ where $X'$ is the set of limit points of $X$.

  We will show that in every partition of $Y = E union F$ into two nonempty disjoint sets, one contains a limit point of the other.

  Suppose that some points of $X$ are in $E$, while others are in $F$. Then since $X$ is connected we are done: we know that one of $X inter E$ and $X inter F$ must contain a limit point of the other.

  Otherwise suppose that all of $X$ falls in one partition, say $E$. Then at least one point of $X'$ has to go in $F$ in order for $F$ to be nonempty. But then $F$ contains a limit point of $E$. So $Y$ is connected.
]

#theorem[
  $overline(C) inter A = C$.
]
#proof[
  By the lemma above, since $C$ is connected, $overline(C) inter A$ is connected. Since it is a connected subset of $A$ that contains $a$, it must be a subset of $C$. But it contains all of $C$. So it just equals $C$.
]

== (d)
The connected components of $(1,2) union (2,3)$ are $(1,2)$ and $(2,3)$: as intervals they are connected, and they're separated since $overline((1,2)) inter (2,3) = (1,2) inter overline((1,2)) = emptyset$.

$QQ$ is totally disconnected, so its connected components are the singleton sets ${q}$ for every $q in QQ$.

== (e)
#theorem[
  If $A$ has finitely many connected components, then for each connected component $C$, there exists an open set $C'' subset.eq RR$ such that $C = C'' inter A$.
]

#proof[
  Let $scr(S)$ be the collection of all the _other_ connected components of $A$ besides C, and write $M_i$ for any member of $scr(S)$.
  
  Since every point of $A$ is in some equivalence class (if only a singleton containing itself), the equivalence classes partition the set, so for the particular component $C$ we can write
  $
    C = & A backslash (union.big scr(S)) \
      = & A inter (union.big scr(S))^C \
      = & A inter (inter.big M_i^C) .
  $
  By the final conclusion of (c), each $M_i = M'_i inter A$ where $M'_i subset.eq RR$ is closed. So
  $
    C = & A inter (inter.big (M'_i inter A)^C) \
      = & A inter (inter.big (M'_i^C union A^C)) \
      = & A inter (A^C union (inter.big M'_i^C)) \
      = & (A inter A^C) union (A inter (inter.big M'_i^C)) \
      = & A inter (inter.big M'_i^C) \
      = & A inter (inter.big M''_i) \
      = & A inter C''
  $
  where each $M''_i eq.triple M'_i^C$ is open since $M'_i$ is closed, and
  $
    C'' eq.triple inter.big M''_i
  $
  where the intersection is finite, so $C'' subset.eq RR$ is open.
]

The finiteness assumption is necessary: take $A = QQ$ which has infinitely many connected components. Every connected component of it consists of the singleton set ${q}$ where $q in QQ$. But there is no open set $C''$ in $RR$ such that
$
  {q} = QQ inter C''
$
because every open set in $RR$ contains an open ball, and by the density of $QQ$ in $RR$, every ball contains an infinite number of points of $QQ$.
