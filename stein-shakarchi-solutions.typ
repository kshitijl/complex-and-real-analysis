#set page(numbering: "1")
#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let lemma = thmbox("lemma", "Lemma", base: none)
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

#align(center)[
  #text(size: 24pt, weight: "bold")[Notes on some exercises and problems from Stein and Shakarchi's _Complex Analysis_]
]

#outline(depth: 2)

= Chapter 1: Preliminaries to Complex Analysis

== Exercise 1

=== (a)
$abs(z-z_1) = abs(z-z_2)$ where $z_1, z_2 in CC$

This is the line passing through the point $frac(z_1+z_2,2)$ and perpendicular to the line from $z_1$ to $z_2$.

=== (b)
$frac(1,z) = overline(z)$

$z=0$ can never be a solution of this equation, so we may multiply both sides by $z$ to obtain
$
   & z overline(z) = 1 \
=> & x^2 + y^2 = 1
$

So this is the circle of radius $1$ centered at the origin.

=== (c)

$"Re"(z) = 3$ is a vertical line 3 units to the right of the imaginary axis.

=== (d)
$"Re"(z) > c$ is the open half-plane to the right of the line $"Re"(z) = c$.

$"Re(z)" >= c$ is the corresponding closed half-plane. In other words, the line $"Re"(z) = c$ itself is included.

=== (e)
$"Re"(a z + b) > 0$ where $a,b in CC$

If $a = 0$ and $"Re"(b) > 0$ then then this is all of $CC$: the equation is true for every $z in CC$.

If $a = 0$ and $"Re"(b) <= 0$ then no points satisfy this equation.

If $a != 0$ then this is the open half-plane to the right of the line passing through $frac(-b,a)$, with a slope that I was too lazy to work out.

=== (f)

$
   & abs(z)      = "Re"(z) + 1 \
=> & abs(z)^2    = "Re"(z)^2 + 1 + 2 "Re"(z) \
=> & x^2 + y^2 = x^2 + 1 + 2 x \
=> & y^2 = 2x + 1
$

This is a parabola opening to the right, passing through the real axis at $- frac(1,2)$ and the imaginary axis at $plus.minus 1$.

=== (g)

$"Im"(z) = c, c in RR$

This is a horizontal line passing through $z = i c$

== Exercise 2

$chevron.l z,w chevron.r$ is defined as $x_1 x_2 + y_1 y_2$, and $(z,w)$ is defined as $z overline(w)$. This is called Hermitian because $(z,w) = overline((w,z))$ for all $z,w in CC$.

The desired result follows from just algebra:
$
   & frac(1,2)[(z,w) + (w,z)] \
= & frac(1,2)[(z,w) + overline((z,w))] \
= & frac(1,2)[(z,w) + overline(z overline(w))]
$

At this juncture, let's note that for any $a in CC$,
$
  a + overline(a) = x + i y + x - i y = 2 "Re"(a) ,
$

so the expression before this becomes
$
  frac(1,2)[2 "Re"(z,w)] = "Re"(z,w) 
$

as desired.

Now,
$
  & "Re"(z,w) \
 = & "Re"(z overline(w)) \
 = & "Re"((x_1 + i y_1) (x_2 - i y_2)) \
 = & "Re"(x_1 x_2 - i x_1 y_2 + i y_1 x_2 + y_1 y_2) \
 = & x_1 x_2 + y_1 y_2 \
 = & chevron.l z,w chevron.r
$

as desired.

== Exercise 3

Let $w = s e^(i theta), s >= 0, theta in [-pi, pi]$.

We want to solve $z^n = w$.

The answer is
$
  z = s^(frac(1,n)) e^(i x)
$

where

$
  n x = theta + 2 pi m, m in NN
$

so
$
  x = frac(theta,n) + m frac(2 pi, n) , m = 0, 1, ..., n-1 .
$

There are $n$ distinct solutions.

== Exercise 4

Suppose $i succ 0$. Then
$
   & i^2 succ 0 \
=> & -1 succ 0 \
=> & -i succ 0 \
=> & i - i succ i \
=> & 0 succ i ,
$

a contradiction.

But if $0 succ i$ then
$
   & 0 - i succ i - i \
=> & -i succ 0   
$

so we may multiply an inequality of the form $ a succ b$ with $-i$ on both sides, which we do to $-i succ 0$ itself to obtain
$
   & (-i)(-i) succ 0 \
=> & -1 succ 0 \
=> & (-1)(-i) succ 0 \
=> & i succ 0 ,
$

a contradiction.

But $i != 0$, so no ordering between $i$ and $0$ is possible, so no total ordering on $CC$ is possible.

== Exercise 5

The key ideas in this exercise are:
- $Omega$ being open allows us to force open a toehold of neighborhood of a point.
- The paths are continuous, so the pre-images of those open neighborhoods will be open.
- In these nicely behaved spaces where smoothness makes sense, the neighborhoods are convex, so we may join points within them with straight lines that stay within the neighborhood.
- Paths can be concatenated.

=== (a)

By the definition of path-connectedness, $z$ is piecewise-smooth, so it must be continuous.

Also by the definition of path-connectedness, $z(t) in Omega$ for every $t in [0,1]$. In particular, the point $z(t^*) in Omega$. Since $Omega$ is the disjoint union of $Omega_1$ and $Omega_2$, the point $z(t^*)$ must be in exactly one of the two.

If $z(t^*) in Omega_1$ then, because $Omega_1$ is open, there must be a neighborhood $N$ of $z(t^*)$ contained in $Omega_1$. $N$ is open and $z$ is continuous, so the pre-image of $N$ under $z$ must be open. Let $z^(-1)(N)$ be that pre-image. We know that $t^* in z^(-1)(N)$ since $z(t^*) in N$. But since $z^(-1)(N)$ is open, there's a neighborhood of $t^*$ contained in it. This gives us a point $t_1 > t^*$ such that $z(t_1) subset N subset Omega_1$, contradicting that $t^*$ is the supremum, for it would no longer be an upper bound.

If $z(t^*) in Omega_2$ then there's an open neighborhood $N$ of $z(t^*)$ contained in $Omega_2$. Its pre-image under $z$ must be open, i.e., we have an open neighborhood $z^(-1)(N) subset [0,1]$ of $t^*$. So there's some $s < t^*$ such that $z(s) in Omega_2$. But this contradicts the definition of $t^*$, for the set that it's the supremum of, is ${t: z(s) in Omega_1 "for all" 0 <= s < t}$. In other words, it's a LEAST upper bound, so every interval below it should should have elements of the set it's a supremum of, but we found an interval that has no members in that set. 

=== (b)

Let $Omega_1 subset.eq Omega$ denote the set of all points that can be joined to $w$ by a curve contained in $Omega$, and let $Omega_2 subset.eq Omega$ denote the set of all points that cannot be joined to $w$ by a curve in $Omega$.

If $x$ is a point in $Omega_1$ then it is also a point in $Omega$. Since $Omega$ is open, there is a neighborhood $N_x subset.eq Omega$. Let $y in N_x$ be another point in that neighborhood. Since $z$ is piecewise smooth, we are working in some kind of smooth manifold, so $N_x$ is convex and we may join $x$ to $y$ by a line contained in $N_x$, which means it is contained in $Omega$. But $x$ was in $Omega_1$, so there's a path from $w$ to $x$, so by concatenating the line, we now have a path from $w$ to $y$ that is contained in $Omega$, so $y in Omega_1$. Here, $y$ was an arbitrary point in the neighborhood $N_x$, so $N_x subset.eq Omega_1$, proving that $Omega_1$ is open.

Suppose $x$ is a point $Omega_2$. Then since $x in Omega$ and $Omega$ is open, there is a neighborhood $N_x subset.eq Omega$ containing $x$. Let $y in N_x$ be another point in that neighborhood. Suppose $y in.not Omega_2$. Then $y in Omega_1$ because $Omega$ is a disjoint union of the two. But then we can join $w$ to $y$ (by the definition of $Omega_1$) and $x$ to $y$ by a line (because $N_x$ is convex), contradicting the definition of $Omega_2$. Therefore $y in Omega_2$. Since $y$ was any point in $N_x$, this proves that $Omega_2$ is open.

Since $Omega$ was connected, and $Omega_1$ and $Omega_2$ are open and disjoint, and $w in Omega_1$ so it's nonempty, then $Omega_1$ must be all of $Omega$. Therefore $Omega$ is pathwise connected.

== Exercise 6

$Omega subset.eq CC$ and $z in Omega$. Component: set $C_z$ of points $w$ in $Omega$ that can be joined to $z$ by a curve entirely in $Omega$.

=== (a)

Want to show $C_z$ is open and connected.

==== Open

Take $w in C_z$. Since $Omega$ is open there's an $r > 0$ such that $D_r(w) subset Omega$. Since discs are convex, straight line paths lie entirely within them; for any $x in D_r(w)$, the path
$
  z(t) = w + t(x-w)
$
goes from $w$ to $x$ and is contained in $D_r(w) subset Omega$.

Therefore $x in C_z$ by concatenating $z arrow.squiggly x$.

Therefore $D_r(w) subset C_z$ whenever $w in C_z$, so $C_z$ is open.

==== Connected

Suppose $C_z = U + V$ where $U$ and $V$ are nonempty, open and disjoint. Take $u in U$ and $v in V$. Then $u arrow.squiggly z arrow.squiggly v$ is a path from $U$ to $V$ contained entirely in $Omega$. Let $f$ be a parameterization of this curve:
$
  f: [0,1] -> Omega, f(0) = u, f(1) = v .
$

Since $[0,1]$ is connected and $f$ is continuous, $f([0,1])$, its image under f, is connected. Let $W$ be that image.

Consider $W inter U$ and $W inter V$. These sets are nonempty (since $u$ and $v$ lie in them), disjoint (since $U$ and $V$ disjoint) and also open in $W$ since they are the intersection of an open set in $Omega$ with the subspace $W$. Thus $W$ is disconnected, a contradiction. Therefore $C_z$ is connected.

==== Equivalence relation

i) $z in C_z$ since the constant/null/identity path that takes $z$ to $z$ is entirely contained in $Omega$.

ii) $w in C_z$ implies that the path $z arrow.squiggly w$ is in $Omega$ which implies that the path $w arrow.squiggly z$ is in $Omega$ which implies that $z in C_w$.

iii) $w in C_z$ so the path $z arrow.squiggly w$ is in $Omega$;

$z in C_(zeta)$ so the path $zeta arrow.squiggly z$ is in $Omega$.

Then, the path $zeta arrow.squiggly z arrow.squiggly w$ is in $Omega$, so $w in C_(zeta)$.

So $w in C_z$ is an equivalence relation.

=== (b)

Suppose $Omega$ had uncountably many distinct connected components. Since each component is open, there's an open ball in each one. Since the components are disjoint, the balls are disjoint. But since the rationals are dense in the reals, each ball contains a point with rational coordinates. So we have an uncountable number of distinct rational numbers, a contradiction of the fact that the rationals are countable.

=== (c)

Take a disc centered at the origin, big enough that it contains $Omega^C$; this is possible since $Omega^C$ is compact.

Everything outside this disc is in $Omega$, since everything not in $Omega$ is within the disc.

Every pair of points $a,b$ outside the disc can be connected by a path in $Omega$: first go radially out or in from $a$ until you're at the same distance from the origin as $b$; then around in a big circle to get to $b$. 

So everything outsid the disc is pat of one connected component, since being in a connected component is an equivalence relation.

Suppose there as another connected component. Then it cannot be outside the disc, because all points outside the disc are in one connected component. Therefore it must be inside the disc. Therefore it is bounded.

Thus $Omega$ can have only one unbounded component.

== Exercise 7

The key step here is to work backwards from the desired algebraic fact to find the terms that must be magically pulled out of a hat in order to factorize.

=== (a)

First let's rotate the whole plane so that $z$ becomes purely real.

Write $z = r e^(i theta)$. Then note that
$
  abs(frac(w-z, 1 - overline(w) z)) = abs(frac(e^(-i theta) w - e^(-i theta) z, 1 - overline(e^(-i theta) w) e^(-i theta) z))
$

because $abs(a b) = abs(a) abs(b)$ and $abs(e^(i theta)) = 1$.

The expression above simplifies to
$
  abs(frac(e^(-i theta) w - r,1 - e^(-i theta)w r)) = abs(frac(w' -r, 1- w' r))
$

where $w' = e^(-i theta) w$.

Now, since $abs(w')=abs(w)$, the expressions for bounds of $abs(w)$ and $abs(z)$ remain unchanged.

So
$
  abs(frac(w-r, 1-overline(w)r)) = frac(sqrt((w-r)(overline(w)-r)), sqrt((1-w r)(1-overline(w) r))) .
$

Write
$
  x = (r-w)
$

so that
$
  overline(x) = (r - overline(w)) .
$

Then
$
  x overline(x) = abs(x)^2 = (r-w)(r-overline(w)) >= 0 .
$

Similarly by defining $y = (1-r w)$ we see that $(1-r w)(1 - r overline(w)) >= 0$.

Now for some algebra. When $abs(r) < 1$ and $abs(w) < 1$, we see that
$
  0 < 1 - r^2
$
and
$
  0 < 1 - abs(w)^2 .
$

So
$
   & (1 - abs(w)^2)(1-r^2) > 0) \
=> & 1 + r^2 abs(w)^2 > r^2 + abs(w)^2 \
=> & 1 + r^2 abs(w)^2 - r overline(w) - r w > r^2 + abs(w)^2 - r overline(w) - r w \
=> & (1 - r w)(1 - r overline(w)) > (r - w) (r - overline(w)) .
$

While it is presented here in this order, I figured out what I needed to add to both sides by working at it in the opposite order, expanding, and simplifying.

We may divide the LHS by the RHS because of the inequalities above, giving the desired result.

When $abs(w) = 1$ or $abs(r) = 1$ we do the same algebra and obtain equality instead, giving the desired result.

=== (b)

The map $F$ is holomorphic because $f/g$ is holomorphic whenever $f$ and $g$ are holomorphic and $g != 0$, which we are guaranteed here by being in the open disc $DD$ and the inequalities proved above.

Also, we compute that $F compose F$ is the identity function, there $F$ is a bijection.

== Exercise 8

I skipped this one because it just seemed like so, so much algebra, and I couldn't figure out how to do it in a clean way that wasn't just a mess of computation.

== Exercise 9

I was confused by this exercise for a while. The key steps were
- to define what it means to seek the Cauchy-Riemann equations in polar coordinates
- to use an elementary identity for limits of exponentials.

For the Cauchy-Riemann equations to make sense, we are talking about _real_-valued functions of one _real_ variable, and the relationships between them. In polar coordinates, the definition that makes sense is
$
  f(r,theta) = u(r,theta) + i v(r,theta)
$

where
$
  & u: RR times [-pi,pi] -> RR \
  & v: RR times [-pi,pi] -> RR
$

are the real and imaginary parts of the complex-valued function $f$.

Now we may write the complex derivative of $f$ as
$
  lim_(Delta z -> 0) frac(Delta f, Delta z) = lim_(Delta z -> 0) frac(Delta u + i Delta v, Delta z) .
$

Now we can ape the classic proof of the Cauchy-Riemann equations by computing this limit with $Delta z$ approaching zero in two different ways: as $r$ goes to 0, and as $theta$ goes to 0.

Along $r -> 0$, we get
$
  Delta z = (r + Delta r) e^(i theta) - r e^(i theta) = Delta r e^(i theta)
$

which, with a minimal amount of algebra, gives
$
  f'(z) = frac(1,e^(i theta))(frac(partial u, partial r) + i frac(partial v, partial r)) .
$

The other direction is more interesting. There,
$
  Delta z = r e^(i theta)(e^(i Delta theta) - 1)
$

so

$
  f'(z) = lim(Delta theta -> 0) frac(1,r e^(i theta))[frac(Delta u + i Delta v, Delta theta) frac(Delta theta, e^(i Delta theta) - 1)] .
$

The first factor is just
$
  frac(partial u, partial theta) + i frac(partial v, partial theta)
$

in the limit, while the second evaluates to $frac(1,i)$. I ... didn't necessarily use the most rigorous justification for that. But here, let's take a shot. We define
$
  e^(i theta) = cos theta + i sin theta .
$

Then,
$
  frac(e^(i Delta theta) - 1, Delta theta) = frac(cos Delta theta + i sin Delta theta - 1, Delta theta) = frac(cos Delta theta - 1, Delta theta) + i frac(sin Delta theta, Delta theta) .
$

The second limit is the class elementary trigonometric limit. The first, idk, there's many ways to see that it's zero. L'Hospital's rule, or by expanding the power series for $cos Delta theta$.

Now we need to multiply out the $e^(i theta)$ factor for both of these expressions for $f'(z)$ and equate the real and imaginary parts to get the desired result.

Verifying that $log z$ is holomorphic in the given region reduces to verifying that the partials exist (which reduces to a statement from ordinary real-variable calculus) and that they obey the polar Cauchy-Riemann equations, which they do.

== Exercise 10

Can I really claim to understand what is meant by expressing a function in the variables $z$ and $overline(z)$? No, I cannot. $overline(z)$ is a straight up bijective function of $z$. For the two to be independent variables needs explanation, and I don't have that explanation.
Anyway. I plugged and chugged this problem. The textbook defines the operators
$
  frac(partial, partial z) = frac(1,2)(frac(partial, partial x) + frac(1,i) frac(partial, partial y)) "and" frac(partial, partial overline(z)) = frac(1,2)(frac(partial, partial x) - frac(1,i) frac(partial, partial y))
$

and simply doing the algebra of applying them one after another gives the desires result ... EXCEPT. For the mixed partials to commute, we need them to be continuous. So I think this formula only holds when that's the case?
