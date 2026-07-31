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

= Read 2.5, 2.6, 2.9

= Artin 2.5.1
#problem[
  Prove that the nonempty fibres of a map form a partition of the domain.
]

= Artin 2.5.6
#problem[
  (a) Prove that the relation $x$ conjugate to $y$ in a group $G$ is an equivalence relation on $G$.

  (b) Describe the elements $a$ whose conjugacy class (= equivalence class) consists of the element $a$ alone.
]

= Artin 2.6.2
#problem[
  Prove directly that distinct cosets do not overlap.
]

= Artin 2.6.4
#problem[
  Give an example showing that left cosets and right cosets of $"GL"_2(RR)$ in $"GL"_2(CC)$ are not always equal.
]

= Artin 2.6.5
#problem[
  Let $H, K$ be subgroups of a group $G$ of orders $3,5$ respectively. Prove that $H inter K = {1}$.
]
