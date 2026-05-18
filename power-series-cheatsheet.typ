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

#show title: set text(size: 30pt)
#show title: set align(center)

#title[Power Series and Taylor Series Cheatsheet]

= The Questions

== For power series

1. What happens inside the radius of convergence?
2. What happens at the boundary?

== For Taylor expansions of a function

1. How well does the Taylor polynomial about $x_0$ approximate the function near that point $x_0$?
2. How well does the Taylor polynomial approximate the function at points further away?

= Summary of answers

== Main theorem: there is such a thing as the radius of convergence

For every power series there is a number $R in [0, infinity]$ such that
1. if $abs(x) < R$, the series converges absolutely
2. if $abs(x) > R$, the series diverges
3. at $abs(x) = R$ the question is subtle: it can converge or diverge, independently at each endpoint

$R$ can be computed using the Cauchy-Hadamard formula $1 slash lim sup abs(a_n)^(1 slash n)$. Sometimes the ratio test works as well: if
$
  L = lim abs(a_(n+1)/a_n)
$
exists then $R = 1 slash L$. The limit doesn't always exist though.

== Power series strictly inside the radius of convergence: uniform convergence on compact subsets

The slogan is: *strictly* inside the radius of convergence, it converges *uniformly* on every compact subset, and it converges *absolutely* at every point.

If the series converges at all (i.e., not necessarily absolutely) for some $x_0$, then:

1. It converges absolutely for every $x$ with $abs(x) < abs(x_0)$
2. It converges uniformly on every interval $[-c,c]$ with $0 <= c < abs(x_0)$
3. It converges uniformly for every compact subset of $(-abs(x_0), abs(x_0))$

But it does NOT, in general, converge uniformly on $(-abs(x_0), abs(x_0))$.

As a consequence of uniform convergence, on compact subsets strictly inside the interval of convergence:
1. The function is continuous
2. We can integrate term-by-term

The differentiation story is a little subtler. We can differentiate term-by-term. The radius of convergence of the differentiated series is the same as that of the original series. But behavior at the endpoints may not be the same: it is possible that the original series converges at some endpoint but the differentiated series does not.

== Power series at the boundary: convergence at an endpoint $R$ => uniform convergence on $[0, R]$

Abel's Theorem is the key result. If the series converges for some $x_0 > 0$, then it converges uniformly on $[0, x_0]$. Similarly, if it converges for some $x_0 < 0$, then it converges uniformly on $[x_0, 0]$. This holds for $x_0 = plus.minus R$ as well. But note that the two endpoints can behave differently. If you know it converges at one endpoint, then it converges uniformly on the closed interval _containing that endpoint_.

Why this is important: without it, we'd only have continuity on $(-R,R)$, not at $R$ itself. So we'd know the series converges to _something_ at $x=R$ but wouldn't be able to connect that value to the continuous function on $(-R,R)$. With Abel's Theorem, we get uniform convergence and therefore continuity (and term-by-term integration) on all of $[0,R]$. We can swap the limit $x -> R^-$ and the infinite sum.

As noted above, Abel's Theorem does not automatically imply that the term-by-term differentiated series converges at $x=R$.

== Taylor polynomial near expansion point: best polynomial approximation of given degree

Taylor's Theorem says that $f(x) - T_(n)(x) = o(abs(x-x_0)^n)$, i.e.,
$
  lim_(x -> x_0) frac(f(x) - T_(n)(x), abs(x-x_0)^n) = 0 .
$

The error of the approximation goes to zero faster than $abs(x-x_0)^n$. In other words, the Taylor polynomial is the unique best polynomial approximation of degree at most $n$, specifically _near that point_.

The word "best" here means, in the sense that the error goes to zero faster than $abs(x-x_0)^n$. It's not necessarily the best polynomial approximation in the $L^2$ or $sup$-norm sense on some interval.

Important hypothesis: the function needs to be differentiable $n$ times in a neighborhood of $x_0$.

== Taylor polynomial away from expansion point: different forms of remainder

Lagrange and Cauchy's theorems give different forms of the remainder. Either one can be more or less useful for bounding the error and proving convergence away from the expansion point.

For these, the function needs to be differentiable $n+1$ times.

== Does the Taylor series equal the function?

Not in general. None of these theorems can guarantee it. There exist counterexamples, like
$
  f(x) = cases(
    exp(-1 slash x^2) quad & "if" x != 0,
    0                      & "if" x = 0 .
  )
$

You need to prove that the remainder goes to 0 as $n->infinity$. Pick whatever form of the remainder is most convenient.

A function is called _analytic_ if its Taylor series converges to it in some neighborhood.

A power series defines a function that is analytic, but not every smooth function is analytic.

= Dependency graph of theorems
