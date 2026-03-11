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

= Heine-Borel without sequential compactness
(Exercise 3.3.10 in Abbott)

#definition[
  A set is _compact_ if every open cover of it has a finite subcover. Note that this is different from how Abbott defines compactness in terms of convergent subsequences.

  We make this definition to avoid clunky repetition of the phrase "a set with the property that every open cover has a finite subcover."
]

Let $[a,b]$ be any closed interval in $RR$. Let ${O_lambda: lambda in Lambda}$ be an open cover for $[a,b]$. Define $S$ to be the set of all $x in [a,b]$ such that $[a,x]$ has a finite subcover from ${O_lambda: lambda in Lambda}$.

#lemma[
  $sup S$ exists and satisfies $a <= sup S <= b$.
]
#proof[
  Since ${O_lambda: lambda in Lambda}$ covers $[a,b]$ and $a in [a,b]$, there must be at least one $O_a in {O_lambda}$ that covers $a$. Then the singleton set ${O_a}$ constitutes a finite subcover of $[a,a]$. So $a in S$.

  By the definition of $S$, it consists of points $x in [a,b]$ with a certain property, therefore it is a subset of $[a,b]$. So $b$ is an upper bound for $S$.

  Since $S subset.eq RR$ is nonempty and bounded, it has a least upper bound.

  Since $a in S$ and the supremum is an upper bound, $sup S >= a$.

  Since every $x in S$ satisfies $s <= b$, by an argument from one or two problem sets ago, $sup S <= b$. Combining the two inequalities gives the desired result.
]

#lemma[
  If $x in S$ and $a <= y <= x$ then $y in S$.
]
#proof[
  Since $x in S$, there's a finite subcover of $[a,x]$ from ${O_lambda: lambda in Lambda}$. This finite subcover also covers $[a,y]$ since $[a,y] subset.eq [a,x]$. So $y in S$.
]

#lemma[
  $sup S = b$.
]
#proof[
  Let $s = sup S$.

  By the lemma above, $s in [a,b]$, so there must be at least one $O_s in {O_lambda: lambda in Lambda}$ that covers it. Since $O_s$ is open in $RR$, there's some ball $B_(epsilon)(s)$ centered at $s$ with radius $epsilon$ contained entirely inside $O_s$.

  We may take $epsilon < b-s$ in the rest of the argument.

  Suppose for the sake of contradiction that $s < b$. Then let
  $
    t = s + epsilon/2
  $
  so $t$ satisfies
  $
    s < t < b "and" t in B_(epsilon)(s) .
  $
  Then $t in O_s$ as well, since the whole ball is contained in $O_s$.

  By the definition of the supremum, there's some $y in S$ with $y > s - epsilon/2$. So there's a finite subcover $Phi$ of $[a, y]$.

  By adjoining $O_s$ to $Phi$ we have a finite subcover of $[a,t]$, so $t in S$ but $t > s$, a contradiction of $s$ being an upper bound.

  So $s <= b$ but we have shown that $s < b$ is impossible. So $s = b$.
]

#lemma[
  $[a,b]$ has a finite subcover.
]
#proof[
  There must be at least one $O_b in {O_lambda: lambda in Lambda}$ that covers $b$. Since $O_b$ is open, there's some ball $B_(epsilon)(b)$ centered at $b$ with radius $epsilon$ contained entirely inside $O_b$. We may take $epsilon < b-a$, for, if $b=a$ then $[a,a]$ is trivially finitely subcoverable and there is nothing more to prove. Since $b = sup S$, by the definition of the supremum and of the set $S$, there's a finite subcover $Phi$ of $[a, b-epsilon/2]$. By adjoining $O_b$ to $Phi$, we have a finite subcover of $[a,b]$.
]

Several problem sets ago we proved the following statement for sequential compactness. Here's the proof for the definition of compactness based on open covers:

#lemma[
  Any closed subset of a compact set is also compact.
]
#proof[
  Let $K subset.eq RR$ be compact and $L subset.eq K$ a closed subset. Then $L^C$ is open in $RR$. Let $C$ be an open cover of $L$. Then $C union {L^C}$ is an open cover of all of $RR$, and in particular of $K$. By compactness of $K$, there's a finite subcover $Phi$ of $K$ from $C union {L^C}$. 

  Since $L subset.eq K$, $Phi$ covers $L$ as well. If $L^C in.not Phi$ then $Phi subset.eq C$ and is the desired finite subcover of $L$ from $C$. Otherwise, if $L^C in Phi$, then $Phi backslash {L^C}$ still covers $L$ and is still finite, since $L^C$ could not have been used to cover any of $L$. Either way we have found a finite subcover of $L$.
]

#theorem[
  Let $K$ be any closed and bounded subset of $RR$. Then $K$ is compact.
]
#proof[
  Since $K$ is bounded it is contained in some interval $[-M,M]$. The interval is compact, and $K$ is a closed subset of it, so $K$ is compact.
]

= Composition of continuous functions

#theorem[
  Let $f: R^m -> R^n$ and $g: R^l -> R^m$ be continuous. Then $f compose g: R^l -> R^n$ is continuous.
]
#proof[
  Let $N subset.eq R^n$ be closed. Then its preimage $M$ under $f$ is a closed subset of $R^m$. And the preimage of $M$ under $g$ (call it $L$) is a closed subset of $R^l$.

  That is, the preimage under $f compose g$ of any closed $N subset.eq R^n$ is closed. So $f compose g$ is continuous.
]
