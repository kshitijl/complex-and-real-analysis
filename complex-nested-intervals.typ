#set page(numbering: "1")
#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let definition = thmbox("definition", "Definition", base: none)
#let lemma = thmbox("lemma", "Lemma", base: none)
#let theorem = thmbox("theorem", "Theorem", base: none)
#let remark = thmbox("remark", "Remark", base: none)
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

= Nested non-empty compact sets in $CC$ with vanishing diameter contain a unique point

== Proof idea

Create a sequence by picking a point in every set. They're nested so each set contains the entire tail of the sequence. And the diameters are vanishing so the sequence is Cauchy.

== Proof

#definition[
  If $Omega subset.eq CC$ is non-empty then
  $
    "diam"(Omega) = sup_(x,y in Omega) abs(x-y) .
  $
]

#theorem[
  If $Omega_1 supset Omega_2 supset ... supset Omega_n supset ...$ is a sequence of non-empty compact sets in $CC$ with the property that
  $
    "diam"(Omega_n) -> 0 "as" n -> infinity ,
  $
  then there exists a unique point $w in CC$ such that $w in Omega_n$ for all $n$.
]

#proof[
  Choose a point $z_n$ in each $Omega_n$.

  Since $"diam"(Omega_n) -> 0$, the sequence is Cauchy: for any given $epsilon$, we pick $n in NN$ such that $"diam"(Omega_n) < epsilon$. Then for any $k,m >= n$,
  $
    z_k, z_m in Omega_n
  $
  so
  $
    abs(z_k - z_m) <= sup_(x,y in Omega_n) |x-y| = "diam"(Omega_n) .
  $

  Therefore, since $CC$ is complete, $(z_k)$ converges to a limit that we call $w$.

  Now, for any $k,m in NN$ with $k >= m$, we know that $Omega_k subset Omega_m$, so $z_k in Omega_m$. Therefore for each fixed $n in NN$ the points $z_k "s.t." k >= n$ form a sequence in $Omega_n$ that converges to $w$, because it's the tail of a convergent sequence, so it converges to the same limit.

  Since the $Omega_n$ are compact, they are sequentially closed. Therefore, looking at the convergent sequence in each $Omega_n$, its limit is also contained in $Omega_n$. That is, $w in Omega_n$ for all $n$. This proves existence.

  For uniqueness, suppose that $w'$ and $w$ were two distinct points such that $w in Omega_n$ and $w' in Omega_n$ for all $n$. Then set $epsilon = abs(w-w')$ and pick some $N in NN$ such that
  $
    "diam"(Omega_N) < epsilon .
  $
  Then $w, w' in Omega_N$, so
  $
    epsilon = |w-w'| <= sup_(x,y in Omega_N) |x-y| = "diam"(Omega_N) < epsilon ,
  $
  a contradiction.
]

#remark[
  This proof only uses the fact that the sets are sequentially closed. Is the hypothesis that they are compact really necessary?

  Well, the vanishing diameters force the sets to (eventually) become compact. So the sets that the theorem applies to are the same whether we require them to be compact or merely closed.
  The theorem fails (not just for uniqueness but also existence) if the sets are allowed to be unbounded: take
  $
    Omega_n = [n, infinity) ,
  $
  a sequence of nested closed sets with empty intersection.

  One generalization of this theorem, in analogy with the Nested Intervals Property from Abbott's book, would be to drop the vanishing diameters requirement and just require boundedness. Then it would state that a sequence of nested non-empty compact sets has non-empty intersection. But the intersection could contain more than one point, as the trivial example
  $
    Omega_n = [0,1] "for all" n
  $
  shows.

  My careful reading of the proof of Goursat's theorem in my textbook (Stein and Shakarchi's _Complex Analysis_, Chapter 2, Section 1, page 35) seems to show that it would go through just fine without the uniqueness: they just need _some_ point in the interior of every triangle so they can use the fact that it's holomorphic to write it as a constant + linear term + error that goes to 0.
]

