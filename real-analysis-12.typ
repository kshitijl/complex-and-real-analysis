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

Exercises are from Stephen Abbott's _Understanding Analysis_, Second Edition.

I'll state some theorems here from the book that don't have names:

#theorem[6.5.1 If a power series $sum_(n=1)^infinity a_n x^n$ converges at some point $x_0 in RR$, then it converges absolutely for any $x$ satisfying $abs(x) < abs(x_0)$.]

#theorem[6.5.5 If a power series converges pointwise on the set $A subset.eq RR$, then it converges uniformly on any compact set $K subset.eq A$. As a consequence, it is continuous at every point at which it converges.]

= Problem 1: An alternating power series
Exercise 6.5.1

Define the function $g$ by the power series
$
  g(x) = x - x^2/2 + x^3/3 - x^4/4 + dots.c .
$

Let
$
  a_n = (-1)^(n+1) x^n/n .
$
== (a)

Let $x in (-1,1)$. Then $abs(x) < 1$ and
$
  lim_(n->infinity) abs(a_(n+1)/a_n) = lim_(n->infinity) abs(x) abs(n/(n+1)) = abs(x) < 1,
$
so by the Ratio Test the series converges pointwise when $abs(x) < 1$. By Theorem 6.5.5 it converges uniformly on compact subsets of $(-1,1)$ and is continuous on $(-1,1)$.

At $x=1$ the series converges by the Alternating Series Test, since
$
  1 > 1/2 > dots.c > 1/n > dots.c 
$
and $(1/n) -> 0$. So the power series defining $g$ is defined on $(-1, 1]$. By Theorem 6.5.5 it converges uniformly on every compact subset of $(-1, 1]$ and it's continuous on $(-1,1]$. 

At $x=-1$ this is (the negative of) the harmonic series, so it diverges (by the Cauchy Condensation Test). So $g$ is not continuous on $[-1,1]$.

The series cannot converge for any point $x$ with $abs(x) > 1$ because that would imply convergence for all $y$ with $abs(y) < abs(x)$, including $y = -1$, contradicting divergence of the harmonic series.

= Problem 2
Exercise 6.5.2

= Problem 3
Exercise 6.5.3

= Problem 4
Exercise 6.5.5

= Problem 5
Exercise 6.5.7

= Problem 6
Exercise 6.5.8

= Problem 7
Exercise 6.6.3

= Problem 8
Exercise 6.6.5, also Exercise 2.8.7 as a prerequisite

= Problem 9
Exercise 6.6.7

= Problem 10
Exercise 6.6.8

= Problem 11
Exercise 6.6.9

= Problem 12
Exercise 6.6.10
