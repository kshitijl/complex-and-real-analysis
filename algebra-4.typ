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

= Automorphisms of the Klein-4 group
#problem[
  Let $V$ denote the Klein 4-group. Show that $"Aut"(V)$ is isomorphic to $S_3$.
]
#proofidea[
  The Klein-4 group consists of four elements ${e, a, b, c}$ where each of $a$, $b$ and $c$ have order 2, and the product of any two of them is the third:
  $
    a^2 = b^2 = c^2 = e
    "and"
    a b = c, a c = b, b c = a .
  $

  So each of $a$, $b$ and $c$ are basically "the same". So we may permute them in any way we want and end up with the same group. But of course each of them is different than $e$.

  So the set of automorphisms of $V$ is the set of permutations of 3 elements, i.e., $S_3$.
]
#proof[
  Short writeup.

  The Klein-4 group $V$ has exactly three elements of order 2. Any automorphism preserves order and fixes the identity, so it permutes these three elements. This given an injective homomorphism $"Aut"(V) -> S_3$. Conversely, any permutation of the three non-identity elements preserves the multiplication rule (since the product of any two distinct non-identity elements is the third, i.e., we are free to change their labels), hence defines an automorphism.  Therefore the map is surjective and $"Aut"(V) tilde.equiv S_3$.
]
#proof[
  Longer writeup.
  
  Any automorphism $phi: "Aut"(V)$ must send $e |-> e$. Also, automorphisms must preserve order, so $phi$ must map the set ${a, b, c}$ to itself.

  So $phi$ is a permutation of the set ${a, b, c}$.

  This gives a map $Phi: "Aut"(V) -> S_{a,b,c} tilde.equiv S_3$.

  This map $Phi$ is injective: any automorphism is determined by where it sends generators. Since $a$ and $b$ generate $V$ (as $a b = c$), knowing $phi(a)$ and $phi(b)$ determines $phi$ completely. In particular, if $phi$ fixes $a, b, c$ then $phi$ is the identity map. So the map $Phi$ is injective.

  The map $Phi$ is surjective (every permutation of ${a,b,c}$ gives an automorphism): we must check that any permutation $sigma$ of ${a,b,c}$ respects the group operation. Fundamentally this is because the product law is automatically preserved, bcause the same relation holds among any triple of elements.

  Define $phi: V -> V$ by $phi(e) = e$ and $phi(x) = sigma(x) "for" x in {a,b,c}$. Now, the multiplication rule in $V$ is symmetric: the product of any two distinct non-identity elements is the third one. Formally, if $x, y in {a,b,c}$ are distinct then $x y$ is the third element of ${a,b,c}$ and $sigma(x), sigma(y)$ are also distinct, so $sigma(x) sigma(y)$ is the third element as well, which is $sigma(x y)$. The cases where $x = e, y = e$ or $x = y$ (giving $x^2 = e$) are immediate. So $phi$ is a homomorphism, and it's bijective since $sigma$ is, hence an automorphism.

]

= Inverse transpose map
#problem[
  Define $f: "GL"_n(RR) -> "GL"_n(RR)$ by $f(A) = (A^T)^(-1)$ (where $A^T$ is the transpose of $A$). Show that $f$ is an automorphism, but not an inner automorphism for $n >= 1$.
]
#lemma[
  If $A$ is an invertible matrix then the transpose and inverse operations commute.
]
#proof[
  $
    A^T (A^(-1))^T = (A^(-1) A)^T = I
  $
  and  
  $
    (A^(-1))^T A^T = (A A^(-1))^T = I
  $
  therefore
  $
    (A^T)^(-1) = (A^(-1))^T .
  $

  where we have used that $(A B)^T = B^T A^T$.
]

#proof[
  $f$ is a homomorphism:

  $
    f(A B) = ((A B)^T)^(-1) = (B^T A^T)^(-1) = (A^T)^(-1) (B^T)^(-1) = f(A) f(B) .
  $

  $f$ is bijective since we have an inverse, namely $f$ itself, using the lemma proved above.
  Therefore $f$ is an automorphism. But $f$ is not an inner automorphism, for then there would exist a single matrix $B$ such that
  $
    f(A) = B^(-1) A B
  $
  i.e.,
  $
    (A^T)^(-1) = B^(-1) A B .
  $
  That this cannot be so can be seen in a number of ways. For one, consider a diagonal matrix $A = lambda I$ with $lambda > 1$. Then the eigenvalues of the LHS are all $1/lambda$ but those of the RHS are all $lambda$.

  Another way: consider the diagonal matrix $A = lambda I$ with $lambda > 1$. Then the trace of the LHS is $n/lambda$, while the trace of the RHS is $n lambda$.
]

= Artin 1.4.5
#problem[
  Prove that the transpose of a permutation matrix $P$ is its inverse.
]
#proof[
  Every permutation matrix looks like this:
  $
  A = 
  mat(
   bar.v, bar.v, , bar.v;
   bold(v)_1, bold(v)_2, dots, bold(v)_n;
   bar.v, bar.v, , bar.v
  )
  $
  where each $v_i$ is a standard unit basis vector $e_j$, and each standard basis vector appears exactly once. So
  $
    A^T A = 
    mat(
      bar.h, bold(v)_1, bar.h;
      bar.h, bold(v)_2, bar.h;
      ,dots.v,;
      bar.h, bold(v)_n, bar.h;
    )
  mat(
   bar.v, bar.v, , bar.v;
   bold(v)_1, bold(v)_2, dots, bold(v)_n;
   bar.v, bar.v, , bar.v
  )
  $
  so the $i,j$th element of $A^T A$ is $v_i^T v_j$. But that is 1 exactly when $i = j$, and 0 otherwise, since the standard unit basis vectors are orthogonal to each other and each basis vector appears exactly once. So $A^T A = I$, that is, $A^(-1) = A^T$.
]

From the perspective of "matrix-vector multiplication is a linear combination of the columns of a matrix", look at just $A^T v_1$. Here, the entries of $v_1$ are the coefficients in a linear combination of the columns of $A^T$. Now, $v_1$ is all zeroes except at one spot, call it $i$. So we get a 0 for each column, except its $i$'th column. But the $i$'th column of $A^T$ has a 1 in the first row, because that's where $v_1$ is! So $A^T v_1$ has a 1 in the first position and all zeroes below, i.e., the first row of $I$.
