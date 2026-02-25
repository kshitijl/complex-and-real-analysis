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

= Artin 1.1.7 Formula for a matrix power

#theorem[For $n in NN$,
$
  mat(1,1,1;
       ,1,1;
       , ,1)^n 
  =
  mat(1, n, frac(n (n+1),2);
       , 1, n;
       ,  , 1)
$
]
#proof[
  For $n=1$ the theorem is true by inspection.

  Using the inductive hypothesis, for $n+1$ we have
  $
  mat(1,1,1;
       ,1,1;
       , ,1)^(n+1)
  & =
  mat(1,1,1;
       ,1,1;
       , ,1)
  mat(1, n, frac(n (n+1),2);
       , 1, n;
       ,  , 1) \
  & = mat(1, n + 1, frac(n(n+1),2) + n + 1;
           , 1    , n+1;
           ,      , 1) \
  & = mat(1, n + 1, frac((n+1)(n+2),2);
           , 1    , n+1;
           ,      , 1) \
  $
  where I did the matrix multiplication in the second step column-by-column: matrix-vector multiplication is taking linear combinations of the columns of a matrix.
]

= Artin 1.1.16 If $A$ is nilpotent, then $I+A$ is invertible

#theorem[
  If $A$ is nilpotent, then $I+A$ is invertible.
]
We give one proof that comes from noticing an analogy to the geometric series
$
  frac(1,1+x) = 1-x+x^2-x^3+...
$
#proof[
  Notice that if $A^k = 0$ for some $k>0$ then
  $
    &   (I+A)(I - A + A^2 - A^3 + ... + (-1)^(k-1)A^(k-1)) \
    & = I - A + A^2 - A^3 ... + (-1)^(k-1)A^(k-1)) \
    &     + A - A^2 + A^3 ... + (-1)^(k-1)A^k \
    & = I
  $
  because all the terms involving $A$ cancel out, the series terminates after $k$ terms, and the leftover term with $A^k$ is zero.
]

We give another proof via eigenvalues:
#proof[
  If $A^k=0$ for some $k>0$ then its eigenvalues must all be $0$, because suppose $v!=0$ is an eigenvector of $A$ with eigenvalue $lambda$. Then
  $
    A v = lambda v
  $
  so
  $
    A^k v = lambda^k v = 0 
  $
  by multiplying $k$ times on the left by $A$.
  
  Since $v != 0$, it must be that $lambda = 0$.

  Also, if $lambda$ is an eigenvalue of $A$ with eigenvector $v$, then $lambda+mu$ is an eigenvalue of $A+mu I$ with the same eigenvector, since
  $
    (A+mu I)v = A v + mu I v = lambda v + mu v = (lambda+mu) v .
  $
  So the eigenvalues of $I+A$ are all one, so its determinant is one (the determinant is the product of eigenvalues with algebraic multiplicity). Therefore it is invertible.
]

= Artin 1.1.17 Solving matrix equations

== (a)
By doing the algebra in
$
  mat(x_1,y_1,z_1;
      x_2,y_2,z_2)
  mat(2,3;1,2;2,5) = mat(1,0;0,1)
$
we get
$
  y_1 = 5-4x_1 \
  z_1 = frac(-3x_1 -2y_1,5) \
  y_2 = -2 -4x_2 \
  z_2 = frac(-2x_2-y_2,2)
$
for every choice of $x_1$ and $x_2$. So there's an infinite 2D space of solutions.

== (b)
No $C$ can make
$
  A C = I_3
$
hold, because the rank of $A$ is at most 2, so the rank of $A C$ is at most 2, while the rank of $I_3$ is 3.

Intuitively, the columns of $A C$ live inside the column space of $A$; every column of $A C$ is a linear combination of the columns of $A$; the column space of $A C$ is a subspace of the column space of $A$. Any time you multiply by a matrix, at best you keep all the original directions, but potentially you kill some. If some get killed, they can never be revived; they have already been sent to 0.

