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

= There is no divergent monotone sequence with a Cauchy subsequence

#lemma[
  Every subsequence of a divergent monotone sequence is unbounded.
]
#proof[
  Let $(x_n)$ be monotone and divergent. Without loss of generality let it be monotone increasing. Then it is unbounded, for if it were monotone and bounded it would converge, by the Monotone Convergence Theorem.

  Thus, for any $b in RR$ there exists a $k in NN$ such that $x_k > b$.

  Let $(x_n_k)$ be any subsequence of $(x_n)$. Since $(x_n)$ is monotone increasing, we have $x_n_k >= x_k$ for every $k in NN$ because $n_k >= k$.

  So, for any $b in RR$, there exists a $k in NN$ such that
  $
    b < x_k <= x_n_k
  $
  so the subsequence is unbounded.
]

#theorem[
  Every monotone sequence with a Cauchy subsequence converges.
]
#proof[
  Let $(x_n)$ be a monotone sequence with a Cauchy subsequence $(x_n_k)$. Suppose for the sake of contradiction that it were divergent. Then by the lemma above, $(x_n_k)$ must be unbounded, a contradiction since Cauchy sequences are bounded. Therefore $(x_n)$ converges.
]

= $2^n >= n$ for all $n in NN$

#proof[
  We proceed by induction on $n$.

  For $n=1$ we verify: $2^1 = 2 >= 1$.

  Then
  $
    2^(n+1) = 2 dot 2^n >= 2 dot n = n + n >= n + 1
  $
  by the inductive hypothesis and since $n >= 1$ for any natural number.
]

= Cauchy sequences in $RR^n$ converge

#theorem[
  Let $(a_k)$ be a sequence in $RR^n$ with the property that for every $epsilon > 0$ there exists an $N in NN$ such that for all $i,j >= N$ we have
  $
    |a_i - a_j| < epsilon
  $
  where $|dot|$ is the usual Euclidean norm. Then $(a_k)$ converges.
]
#proof[
  We will prove that each coordinate converges, by the Cauchy Criterion in $RR$.
  
  Let $a_k^((l))$ denote the $l$'th coordinate of $a_k$. Let $epsilon > 0$ be given and let $N$ be the corresponding index in $(a_k)$ in the statement of the theorem. Then, since for the usual Euclidean norm $|v^((l))| <= |v|$, for any $i,j >= N$
  $
    |a_i^((l)) - a_j^((l))| <= |a_i - a_j| < epsilon .
  $
  So the sequence $(a_k^((l)))$ in each coordinate $l$ is a Cauchy sequence in $RR$ and therefore converges to a limit $a^((l)) in RR$. By Problem 3 in the first compactness problem set, $(a_k)$ itself converges (to the point in $RR^n$ whose $l$'th coordinate is $a^((l))$).
]
