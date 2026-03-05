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

= Problem 1: $overline(A)$ is closed
(Exercise 3.2.7)

Given $A subset.eq R$, let $L$ be the set of all limit points of $A$.

=== Proof idea

If $x$ is a limit point of $L$, there's always point of $L$ in its neighborhood, no matter how small. Since _that_ point is a limit point of $A$, we can find a point $r$ of $A$ in _its_ neighborhood. Now arrange the neighborhood sizes to make sure $r$ is close to $x$ but can't actually _be_ $x$.

The lemma does this little dance. It's an awkwardly stated lemma because I wanted to be able to use it in both parts without waving my hand and saying, in part (b), "... by pretty much the same argument as part (a)".

== (a)
#lemma[
  Given $q in L$, and any $epsilon > 0$ and a point $x$ different from $q$ with
  $
    abs(x-q) < 1/2 epsilon
  $
  there exists a point $r in A$, different from $x$, satisfying
  $
    abs(x-r) < epsilon .
  $
]

#proof[
  Since $q in L$, it is a limit point of $A$. Let
  $
    delta = min(1/2 epsilon, abs(x-q)/2)
  $

  and take an open ball $B_(delta)(q)$ of radius $delta$ centered at $q$. Then this ball contains a point $r in A$ that's different from $q$.

  By the triangle inequality applied to $x-r = x-q+q-r$,
  $
       & abs(x-r) \
    =  & abs(x-q+q-r) \
    <= & abs(x-q) + abs(q-r) \
    < & 1/2 epsilon + delta \
    <= & 1/2 epsilon + 1/2 epsilon \
    =  & epsilon .
  $

  So $r in B_(epsilon)(x)$. Now we show that $x != r$:

  By the triangle inequality applied to $x-q = x-r+r-q$,
  $
       & abs(x-q) \
    =  & abs(x-r+r-q) \
    <= & abs(x-r) + abs(r-q) .
  $
  Rearranging,
  $
       & abs(x-r) \
    >= & abs(x-q) - abs(r-q) .
  $ <e1>

  By the choice of $delta$,
  $
    abs(r-q) < delta <= abs(x-q)/2
  $
  so
  $
    - abs(r-q) > -abs(x-q)/2 
  $
  which we substitute into @e1 to obtain
  $
    abs(x-r) >= abs(x-q) - abs(r-q) > abs(x-q) - abs(x-q)/2 = abs(x-q)/2 .
  $

  Since $q != x$, the RHS above is a finite positive number, proving that $x != r$.
]

#theorem[
  $L$ is closed.
]
#proof[
  Let $x$ be a limit point of $L$ and let $epsilon$ be given.

  Take a ball $B_(1/2 epsilon)(x)$ of radius $1/2 epsilon$ centered at x. Then this ball contains a point $q in L$ that's different from $x$.

  By the lemma above, there is a point $r in A$, contained in $B_(epsilon)(x)$, that is different from $x$. Thus $x$ is a limit point of $A$, so by the definition of $L$, $x in L$. So $L$ is closed.
]

== (b)
#theorem[
  If $x$ is a limit point of $A union L$, then $x$ is a limit point of $A$. Thus, $overline(A)$ is closed.
]

#proof[
  Suppose $x$ is a limit point of $A union L$ and let $epsilon > 0$ be given. Then the ball $B_(epsilon/2)(x)$ of radius $1/2 epsilon$ centered at $x$ contains a point $q != x$ in $A union L$. So $q$ is either in $A$ or in $L$ or in both. If $q in A$, set $r = q$. Otherwise, if $q in L$, take the $r$ produced by the lemma proved above. Either way, $r$ satisfies the following properties:
  $
    r in A \
    "and" \
    r != x \
    "and" \
    abs(x-r) < epsilon
  $
  proving that $x$ is a limit point of $A$.

  Thus, $x in L subset.eq A union L = overline(A)$, proving that $overline(A)$ is closed.
]

= Problem 2: Existence of sets with certain properties
(Exercise 3.2.10)

=== Proof idea

Part (i) can't happen because $[0,1]$ is compact and complete: sequences inside it can't run away to infinity, and they can't fall into a hole. They can bounce around, but they'd have to pile up _somewhere_. That's a limit point.

Part (ii) can happen: the rationals have no isolated points anywhere, so we can take the rationals inside $[0,1]$.

Part (iii) can't happen. The main idea is that there's a little open ball around each isolated point with no other members of the set within it. This is a ball in $RR$, so it contains a rational point. That's the contradiction: an uncountable number of balls, each with a distinct rational point. We just need to make sure the balls are disjoint so we can argue that every rational we've picked is distinct.

== (i)
A countable (= countably infinite) set contained in $[0,1]$ with no limit points: this cannot exist. A proof is in Problem 6, which shows that every bounded infinite set has a limit point.

== (ii)
Take the set $A = Q inter (0,1)$. By construction, $A subset [0,1]$.

We will show that every point $q in A$ is a limit point:

For any $epsilon > 0$, let $delta = min(epsilon, q, 1-q)$. Then
$
  delta > 0 \
  "since" \
  0 < q < 1 \
$

and the ball $B_(delta)(q)$ is contained in $B_(epsilon)(q) inter (0,1)$.

Then the numbers $a = q + 1/3 delta$ and $b = q + 2/3 delta$ are both contained in $B_(delta)(q)$. By the density of $QQ$ in $RR$, there exists a rational number $a <= r <= b$. But since $q < a$, we have $q < r$. So $q != r$.

Also, $r in [a,b] subset B_(delta)(q) subset.eq (0,1)$. So $r in QQ inter (0,1)$.

We have produced an $r$ such that
$
  r != q \
  "and" \
  r in QQ inter (0,1) = A \
  "and" \
  r in B_(epsilon)(q)
$
so $q$ is a limit point of $A$.

== (iii)
#theorem[
  A set $A in RR$ cannot have an uncountable number of isolated points.
]
#proof[
  Suppose for the sake of contradiction that $A$ has an uncountable number of isolated points. Let $I$ be the set of its isolated points. Then for each $x in I$ there exists an $epsilon_x > 0$ such that the open ball $B_(epsilon_x)(x)$ of radius $epsilon_x$ centered at $x$ has no other points of $A$.

  Define
  $
    r_x = inf{abs(x-y): y in I, y != x} .
  $
  Then $r_x > 0$ for every $x in I$. (Otherwise, if $r_x = 0$, $x$ would not be an isolated point of $A$: by the properties of the infimum, for every $zeta > 0$ there would exist some $y in I subset.eq A$ such that $abs(x-y) < 0 + zeta$, making $x$ a limit point of $A$.)

  Define
  $
    delta_x = 1/2 min(epsilon_x, r_x) > 0 .
  $

  Since $delta_x < epsilon_x$, the open ball $B_(delta_x)(x)$ has no points of $A$ besides $x$.

  Also, since $delta_x <= 1/2 r_x$, for any distinct $x_1, x_2 in I$ we have
  $
    B_(delta_x_1)(x_1) inter B_(delta_x_2)(x_2) = emptyset ,
  $
  because if a point $y$ were in both open balls,
  $
       & abs(x_1 - x_2) \
    =  & abs(x_1 - y + y - x_2) \
    <= & abs(x_1 - y) + abs(x_2 - y) \
    <  & delta_x_1 + delta_x_2 \
    <= & 1/2 r_x_1 + 1/2 r_x_2 \
    <= & 1/2 abs(x_1 - x_2) + 1/2 abs(x_2 - x_1) \
    =  & abs(x_1 - x_2) ,
  $
  a contradiction.

  (Note that $r_x_1 <= abs(x_1 - x_2)$ since $r_x_1$ is the infimum of $abs(x_1 - x_2)$ among _all_ $y in I$, of which $x_2$ is a member.)

  By the density of $QQ$ in $RR$, each $B_(delta_x)(x)$ contains a rational point $q_x$. But since the balls are disjoint, $q_x_1 != q_x_2$ whenever $x_1 != x_2$. That is, we have an injection from the uncountable set $I$ to the countable set $QQ$, a contradiction.
]

#remark[
  Since $I subset.eq A$, the choice of $epsilon_x$ forces all $y in I backslash {x}$ to lie outside $B_(epsilon_x)(x)$, so I think $r_x >= epsilon_x$, and we could get rid of the whole business with $r_x$ and just directly say $delta_x = epsilon_x/2$.
]
#remark[
  Instead of making the balls disjoint, we could also have picked a single rational $r > x$ in each $x$'s neighborhood and prove that it cannot be simultaneously in another $y$'s neighborhood AND bigger than it.
]

= Problem 3: Union of closure
(Exercise 3.2.11)

=== Proof idea

One direction is easy, by using that $overline(A)$ is the smallest closed set containing $A$. To prove the other direction just unwind definitions.

This rule can't extend to infinite unions for the same reason that an infinite union of closed sets cannot be closed: that would imply that every set is closed, since every set is the union of (singleton sets of) its points, and those are closed sets.

== (a)

#theorem[
  $overline(A union B) = overline(A) union overline(B)$
]
#proof[

($subset.eq$)

  Note that the set $overline(A union B)$:
  - is closed, since it is the closure of a set,
  - contains $A union B$, and
  - is the smallest such set.

  while the set $overline(A) union overline(B)$:
  - is closed, since it's the finite union of two closed sets,
  - contains $A$, since it contains $overline(A)$, which contains $A$, and
  - contains $B$.
  - So it contains $A union B$.

  But $overline(A union B)$ is the smallest closed set containing $A union B$. Therefore $overline(A union B) subset.eq overline(A) union overline(B)$.

  ($supset.eq$)

  To prove the other direction, let $x in overline(A) union overline(B)$. Then $x$ belongs to one of $A$, $B$, $L_A$ and $L_B$, where $L_A$ denotes the limit points of $A$ and likewise $L_B$ the limit points of $B$.

  If $x in A$ or $x in B$ then $x in A union B subset.eq overline(A union B)$.

  Suppose without loss of generality that $x in L_A$. Then every $epsilon$-neighborhood of $x$ contains a point $q in A$ that's different from $x$ itself. The point $q in A subset.eq A union B$, which makes $x$ a limit point of $A union B$ as well. So $x in overline(A union B)$.

  We have proved that whenever $x in overline(A) union overline(B)$ then $x in overline(A union B)$. So $overline(A) union overline(B) subset.eq overline(A union B)$. Combined with the previous argument showing inclusion the other way, this shows that $overline(A) union overline(B) = overline(A union B)$.
]

== (b)

This result about closures does not extend to infinite unions of sets. If it did, we would be able to argue that _any_ set is closed by decomposing it as the union of singleton sets of all its points. Each singleton set would be closed and would therefore equal its closure. Then the infinite union of closures of singletons would produce the original set on the RHS. But the LHS of the equation in the theorem is a closed set.

For example, define
$
  A_n = {1/n} .
$
Since the set is a singleton it has no limit points:
$
  overline(A_n) = A_n .
$

Suppose it were true that
$
  overline(union.big_(n=1)^infinity A_n) = union.big_(n=1)^infinity A_n .
$
The LHS is a closed set, while the RHS has the limit point 0 but does not contain it.

= Problem 4: Distance between compact sets
(Exercise 3.3.8)

Let $K$ and $L$ be nonempty compact sets, and define
$
  d = inf {abs(x-y): x in K "and" y in L}
$

=== Proof idea

The way I really want to _think_ about this is the second proof sketched below: $K times L$ is compact and the distance function is continuous, so it achieves its infimum on it.

But at this point of the book we don't have all that machinery. To use compactness, create a sequence of points getting closer and closer to each other by setting $epsilon = 1/n$ and using the property of the infimum that there must be a pair at least that close. This is a sequence of _pairs_, so to use compactness, get a convergent subsequence in the first coordianate, and a subsequence of _that_ that's convergent in the second coordinate, similar to an earlier proof that rectangles in $RR^n$ are compact. Then the first-coordinate subsequence still converges since its mother converges. (This is really the same proof.)

For part (b), we know we've got be looking for an unbounded closed set, and another closed set that gets closer and closer to it out at infinity. So the sets must have "holes" in them where the other can fit. $NN$ seems like a natural fit.

== (a) 
#lemma[
  If $(a_n) -> a$ then $abs(a_n) -> abs(a)$.
]
#proof[
  Let $epsilon$ be given. Then there exists $N in NN$ such that whenever $n >= N$ we have
  $
    abs(a_n - a) < epsilon .
  $
  By the reverse triangle inequality,
  $
    abs(abs(a_n) - abs(a)) <= abs(a_n - a) <= epsilon .
  $
]
#theorem[
  If $K$ and $L$ are disjoint in addition to being nonempty and compact, then the distance $d$ defined above satisfies
  $
    d > 0
  $
  and
  $
    d = abs(x_0 - y_0) "for some" x_0 in K "and" y_0 in L
  $
]
#proof[
  Since $abs(x-y) >= 0$ for all $x in K$ and $y in L$, the infimum of these distances must also be non-negative.
  
  For each $n in NN$ let $epsilon = 1/n$. Then there must exist some $x_n in K$ and $y_n in L$ such that $abs(x_n - y_n) < d + epsilon$, producing sequences $(x_n)$ and $(y_n)$ such that $abs(x_n - y_n) -> d$.

  By compactness of $K$ there's a convergent subsequence of $(x_n)$ converging to some $x_0 in K$. Call it $(x_n_k)$. Let $(y_n_k)$ be the subsequence of $(y_n)$ corresponding to the indices $n_k$ of $(x_n_k)$. Since $L$ is also compact, the sequence $(y_n_k)$ has a convergent subsequence, call it $(y_m_k)$, converging to some $y_0 in L$. Let $(x_m_k)$ be the subsequence of $(x_n_k)$ corresponding to the indices $m_k$ of $(y_m_k)$. Since $(x_m_k)$ is a subsequence of the convergent sequence $(x_n_k)$, it converges to the same limit $x_0 in K$.

  We now have subsequences $(x_m_k) -> x_0 in K$ and $(y_m_k) -> y_0 in L$. Since $(x_m_k, y_m_k)$ is a subsequence of $(x_n, y_n)$, we have $abs(x_m_k - y_m_k) -> d$ as well. So by the Algebraic Limit Theorem and the lemma proved above,
  $
    lim abs(x_m_k - y_m_k) = d = abs(x_0 - y_0) .
  $

  If $d = 0$ then $x_0 = y_0$, but that is impossible since $K$ and $L$ were disjoint. Thus $d != 0$, which, together with $d >= 0$ implies $d > 0$.
]

Here's a proof using tools that we developed in the compactness problem sets but that aren't available at this point yet in Abbott. I found this one a lot easier to come up with. Unfortunately it uses one thing we haven't proved yet, that the composition of continuous functions is continuous:

#proof[
  Consider the set
  $
    K times L = {(x,y): x in K, y in L}
  $
  which can be written as an intersection of two sets:
  $
    K times L = {(x,y): x in K, y in RR} inter {(x,y): x in RR, y in L}
  $
  where each is the preimage of a closed set under a trivial continuous function:
  $
    f_1(x,y) = x \
    "and" \
    f_2(x,y) = y .
  $
  Therefore $K times L$ is closed. Also, it is bounded (since each of $K$ and $L$ is bounded), so it can be enclosed in a closed rectangle in $RR^2$. As a closed subset of a compact set, it is compact.

  (We could also have proved this directly using the sequential definition of compactness I think.)

  The function
  $
    f(x,y) = |x - y|
  $
  is continuous as the composition of the continuous function $(x,y) |-> x - y$ and the absolute value function (proved continuous in the lemma above). Therefore it achieves its infimum on the compact set $K times L$, producing the required $(x_0, y_0)$.

  From here we prove that $d >= 0$ and $d != 0$ much the same as before.
]

== (b)
Let
$
  K = {n: n in NN "and" n >= 2}
$
and
$
  L = {n + 1/n: n in NN "and" n >= 2} .
$

Then $K$ and $L$ are disjoint. They are both closed sets since all their points are isolated, being at least a distance of 1 away from any other element. So they have no limit points, so they contain all their limit points, so they're closed.

Now
$
  d = inf{abs(x-y): x in K "and" y in L} <= inf{abs(n+1/n-n): n in NN} = 0 .
$

= Problem 5: Closed and bounded $=>$ every open cover has a finite subcover
(Exercise 3.3.9)

=== Proof idea

This reminded me of the proof that the union of two closed sets is closed, where a sequence in $A union B$ must have infinity terms in at least one of $A$ and $B$. The analogy isn't precise, but it helped me come up with the main idea here which is: if a set cannot be finitely subcovered, then at least one of its halves also cannot be finitely subcovered.

== Proof

#theorem[
  Let $K$ be a sequentially compact, closed and bounded set. Then every open cover for $K$ has a finite subcover.
]
#proof[
  Let ${O_lambda: lambda in Lambda}$ be an open cover for $K$. For contradiction, let's assume that no finite subcover exists. Let $I_0 = [a,b]$ be a closed interval containing $K$; such an interval must exist because $K$ is bounded.

  Consider the left and right halves of $I_0$: $I_0^L = [a, (a+b)/2]$ and $I_0^R = [(a+b)/2,b]$. Then at least one of $I_0^L inter K$ and $I_0^R inter K$ cannot be finitely subcovered by the  $O_lambda$, because otherwise the union of the two finite subcovers would constitute a finite subcover of $K$.

  Choose $I_1$ to be any half of $I_0$ such that $I_1 inter K$ cannot be finitely subcovered. Proceeding in this way, choose $I_n$ to be any half of $I_(n-1)$ such that $I_n inter K$ cannot be finitely subcovered by the $O_lambda$.

  Thus $I_0 supset.eq I_1 supset.eq ... supset.eq I_n ...$ is a nested sequence of closed intervals such that, for each $n$, $I_n inter K$ cannot be finitely subcovered and $abs(I_n) = abs(I_(n-1))/2$ so $lim abs(I_n) -> 0$.

  Each $I_n$ is a closed interval, therefore closed and bounded. Therefore $I_n inter K$ is also closed and bounded and therefore sequentially compact. It is also nonempty, since otherwise it would have a trivial finite subcover. And $(I_n inter K) supset.eq (I_(n+1) inter K)$ for each $n$. Therefore by the Nested Compact Set Property, there exists some
  $
    x in inter.big_(n=1)^infinity (I_n inter K) .
  $
  Then $x in I_n$ for each $n$, and $x in K$.

  Because $x in K$, there must exist an open set $O_(lambda_0)$ from the original collection that contains $x$ as an element. Since the set is open, there's some open ball $B_(epsilon)(x) subset.eq O_(lambda_0)$ centered at $x$ and with radius $epsilon$. Then there's an interval $I_(n_0)$ whose width is smaller than $epsilon$, that contains $x$, therefore it's entirely inside this ball. So the open set $O_(lambda_0)$ covers all of $I_(n_0)$, therefore it covers all of $I_(n_0) inter K$, which would be a finite subcover of $I_(n_0) inter K$, a contradiction of its construction.
]

= Problem 6: Every bounded infinite set has a limit point
(Exercise 3.3.12)

== Proof idea

If a set has no limit points then all its points are isolated, and isolated means we can put an open ball around each one that contains no other point from the set. This leads naturally to a contradiction.

== Proof

#theorem[
  Every bounded infinite set has a limit point.
]
#proof[
  Let $A$ be a bounded infinite set. Suppose for the sake of contradiction that it had no limit points. Then it contains all its limit points, so it's closed. By the Heine-Borel Theorem, since $A$ is closed and bounded, every open cover of $A$ has a finite subcover.
  
  Also, since $A$ has no limit points, every point in it is an isolated point. So for each point $x in A$, there exists an $epsilon$ such that the open ball $O_x = {y in RR: |x-y| < epsilon}$ contains no points of $A$ besides $x$.

  The collection ${O_x: x in A}$ then forms an open cover. Let $B = {O_x_1, O_x_2, ..., O_x_n}$ be a finite subcover. But by construction, each $O_x$ contains exactly one point of $A$, so the union of all sets in $B$ contains only finitely many points of $A$, a contradiction.
]

Just for fun here's the proof using sequences and the Bolzano-Weierstrass Theorem instead of open covers and Heine-Borel:

#proof[
  Let $A$ be a bounded infinite set. Construct the sequence $(x_n)$ as follows: let $x_1$ be any point in $A$. For $x_2$, pick any point in $A$ different from $x_1$, which is possible since $A$ has infinitely many points. In this way, for $x_n$ pick any point of $A$ not in ${x_i: i < n}$, which must be possible since $A$ is infinite.

  By construction, every point of $(x_n)$ is distinct and contained in $A$. Since the set $A$ is bounded, so is the sequence $(x_n)$. By the Bolzano-Weierstrass Theorem, it has a convergent subsequence $(x_n_k)$ whose limit we shall call $x$.

  Let $epsilon$ be given. Consider a ball $B_(epsilon)(x)$ of radius $epsilon$ centered at $x$. Since all the $(x_n_k)$ are distinct and, by convergence of $(x_n_k)$ to $x$, infinitely many lie in $B_(epsilon)(x)$, there must be one different from $x$. And every $x_n_k in A$. We have proved that for every $epsilon$, $B_(epsilon)(x)$ contains a point of $A$ different from $x$, i.e., that $x$ is a limit point of $A$.
]


