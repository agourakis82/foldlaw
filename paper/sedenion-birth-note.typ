#set document(
  title: "Birth off the basis: the anti-associator and associator kernels of every quaternionic pair of sedenions",
  author: "Demetrios C. Agourakis",
  date: datetime(year: 2026, month: 10, day: 3),
)
#set page(margin: (x: 2.5cm, y: 2.5cm), numbering: "1")
#set text(font: "New Computer Modern", size: 10pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.")
#set math.equation(numbering: "(1)")

#let thm(kind, name, body) = block(width: 100%, inset: (y: 0.4em))[
  #text(weight: "bold")[#kind#if name != none [ (#name)].] #body
]

#align(center)[
  #text(14pt, weight: "bold")[Birth off the basis:\ the anti-associator and associator kernels\ of every quaternionic pair of sedenions]
  #v(0.8em)
  #text(11pt)[Demetrios C. Agourakis]
  #v(0.3em)
  #text(9pt)[PUC-SP, Sorocaba; Faculdade São Leopoldo Mandic, Campinas. ORCID 0009-0001-8671-8878]
  #v(0.3em)
  #text(9pt)[3 October 2026 — research note, companion to _The Birth Function_ (preprint v1)]
]

#v(0.8em)
#block(width: 100%, inset: (x: 1cm, y: 0.6cm), stroke: 0.5pt)[
  #text(weight: "bold")[Summary.]
  In _The Birth Function_ the dimension of the anti-associator kernel $"Ass"'[e_a, e_b]$ was computed for every pair of basis units of every Cayley–Dickson algebra. This note leaves the basis. For an arbitrary quaternionic pair $(x,y)$ of the sedenions $SS = A_4$ -- the first level at which quaternionic pairs exist that are not lifts of octonion pairs -- we prove that the pair lies in an octonion subalgebra $E = Q plus.o Q ell$ over a quaternion subalgebra $Q subset OO$, that both kernels split along $E plus.o E^perp$, that the $E$-halves contribute $4 + 4$, and that the $E^perp$-halves are governed by two explicit quaternion matrices. The result is a closed formula: $dim "Ass"'[x,y] = 4 + 8 dot bb(1)[r = 0]$ with $r = [c,b] + [a,d]$, and $dim "Ass"[x,y] = 4 + 4(2 - "rk"_HH M)$ with $M$ a $2 times 2$ quaternion matrix written out below. Consequences: $dim "Ass"' in {4, 12}$ for every quaternionic pair of $SS$ (the mod-8 law survives off the basis), $dim "Ass" in {4, 8, 12}$ (it does not), all six combinations occur, the defect $dim "Ass" + dim "Ass"' - 16$ takes exactly the values ${-8,-4,0,4,8}$, the generic pair has $(4,4)$, and the basis pairs are the defect-zero stratum. The quantity $r$ is the polarisation of Moreno's alternativity obstruction: for alternative $x, y$ the kernel is $12$-dimensional exactly when $x + y$ is alternative. Section 5 lifts the mechanism to every level for quaternionic pairs of alternative elements: by Moreno's classification the pair lies in an iterated double $Q^(2^(m-3)) tilde.equiv A_(m-1)$, both kernels split along a tower of such subalgebras, and each kernel is $4$ plus a sum of block kernels, one per level, each a multiple of $4$. For basis units at level $5$ the blocks are exactly the binary digits of the bin index of _The Birth Function_; off the basis a half block occurs. The multiple of $8$ does not survive: the pair $x = e_3 - e_(16) - 2 e_(19)$, $y = e_2 - e_3 - 2 e_(10) + 2 e_(11) - e_(16)$ has $dim "Ass"' = 8$ and top block $4$. Section 6 closes level $5$: the top block is a $2 times 2$ quaternion matrix problem with explicit entries in Moreno's parameters, $beta_5 in {0, 4, 8, 16}$, and $dim "Ass"' in {4, 8, 12, 20, 28}$ for every quaternionic pair of alternative elements of $A_5$ -- $16$ and $24$ never occur. Hand proofs; every step checked by exact integer computation ($27 thin 413$ pairs at level $4$, $465 + 4002 + 6000$ at level $5$, $2000$ at level $6$, $400$ at level $7$). Not formalised.
]

= Setting and statement

Write $SS = OO times OO$ with the product of _The Birth Function_, eq. (mul):
$ (x, y)(a, b) = (x a - b overline(y), thick overline(x) b + a y), quad overline((x,y)) = (overline(x), -y). $ <eq:mul>
An element $(a,b)$ is imaginary iff $a in "Im" thin OO$; $b$ is unrestricted. We write $b = b_0 + arrow(b)$ for the real and imaginary parts of $b in OO$, and $u times v$, $⟨u, v⟩$ for the cross product and inner product of imaginary elements of a quaternion subalgebra, so that $u v = -⟨u,v⟩ + u times v$ there. The associator is $[x,z,y] = (x z) y - x (z y)$, the anti-associator $W_(x,y)(z) = (x z) y + x(z y)$; $"Ass"[x,y] = ker [x, dot, y]$ and $"Ass"'[x,y] = ker W_(x,y)$, as in Biss–Dugger–Isaksen #cite(<bissDuggerIsaksen2008>) (BDI), Definition 8.1. A _quaternionic pair_ (BDI, Definition 4.6) is a pair of nonzero orthogonal imaginary elements with $[x,x,y] = 0 = [y,y,x]$.

#thm("Theorem 1", [birth at the sedenions, off the basis])[Let $(x,y)$ be a quaternionic pair in $SS$.

(i) _Containment._ There is a quaternion subalgebra $Q subset OO$ such that $x = (a,b)$, $y = (c,d)$ with $a, c in "Im" thin Q$ and $b, d in Q$. Orthogonality reads $⟨a,c⟩ + ⟨b,d⟩ = 0$.

(ii) _Anti-associator._ With $r := [c,b] + [a,d] = 2(c times arrow(b) + a times arrow(d)) in "Im" thin Q$,
$ dim "Ass"'[x,y] = 4 + 8 dot bb(1)[r = 0]. $ <eq:N>

(iii) _Associator._ Put $p = a times c + arrow(b) times arrow(d)$, $q = d_0 arrow(b) - b_0 arrow(d)$, $w = d_0 a - b_0 c$ (all in $"Im" thin Q$) and $t = ⟨a, arrow(d)⟩ - ⟨arrow(b), c⟩ in RR$, and let
$ M = mat(p + q, w + t; w - t, p - q) $ <eq:M>
act on $Q times Q$ by left multiplication, $(u,v) arrow.r.bar ((p+q) u + (w+t) v, thick (w-t) u + (p-q) v)$. Then
$ dim "Ass"[x,y] = 4 + 4 (2 - "rk"_HH M) = 4 + dim_RR ker M in {4, 8, 12}. $ <eq:A>
In particular $dim "Ass"[x,y] = 12$ iff $p = q = w = 0$ and $t = 0$; and $"rk"_HH M = 1$ iff $M eq.not 0$ and $|p+q|^2 |p-q|^2 + |w+t|^2 |w-t|^2 = 2 thin "Re"(overline((p-q)) (w-t) overline((p+q)) (w+t))$ (the Study determinant).]

#thm("Corollary 1", [values and defect])[For every quaternionic pair of $SS$: $dim "Ass"' in {4,12}$, $dim "Ass" in {4,8,12}$, and all six combinations occur. The defect $delta(x,y) := dim "Ass"[x,y] + dim "Ass"'[x,y] - 16$ takes exactly the values $-8, -4, 0, 4, 8$. A generic pair (Zariski-open in the pairs of $"Im" E$) has $(dim "Ass"', dim "Ass") = (4,4)$, $delta = -8$. The basis pairs, and every pair reached by BDI's lifting lemmas 8.7–8.10 from the octonions, have $delta = 0$.]

#thm("Corollary 2", [the mod-8 law off the basis])[$dim "Ass"'[x,y] equiv 4 (mod 8)$ for every quaternionic pair of $SS$, not only for pairs of basis units. The companion statement for the associator fails: $dim "Ass"[x,y] = 8$ occurs (e.g. $x = e_1 - e_8$, $y = e_2 - e_9$).]

#thm("Corollary 3", [alternativity reading])[For $z = (a,b) in "Im" thin SS$ let $nu(z) = [a,b] in "Im" thin OO$. By Moreno #cite(<moreno2004alt>) (Theorem 3.3 with Proposition 3.1), $z$ is alternative iff $nu(z) = 0$. Since $nu$ is quadratic, $r = nu(x+y) - nu(x) - nu(y)$, so for a quaternionic pair of _alternative_ elements -- the setting of BDI Section 11 --
$ dim "Ass"'[x,y] = cases(12 & "if" x + y "is alternative", 4 & "otherwise"), $
and by BDI Proposition 11.1 the annihilator of $x + y ell'$ in $A_5$ has that dimension.]

#thm("Corollary 4", [propagation])[By BDI Lemmas 8.7–8.10, the four lifts of $(x,y)$ to $A_5$ have $(dim "Ass"', dim "Ass")$ equal to $(2N+4, 2A-4)$ for the same-side lifts and $(2A-4, 2N+4)$ for the cross lifts, where $(N,A)$ are the values of Theorem 1; hence $delta$ doubles at each lift and the pairs of $A_m$ obtained by lifting from $SS$ have defects $2^(m-4) dot {-8,-4,0,4,8}$.]

= Proof

*Lemma A (containment).* _If $x, y in "Im" thin SS$ satisfy $[x,x,y] = 0 = [y,y,x]$, then $x, y in Q times Q$ for some quaternion subalgebra $Q subset OO$._

Let $x = (a,b)$, $y = (u,v)$ with $a in "Im" thin OO$. By @eq:mul, $x^2 = (a^2 - b overline(b), overline(a) b + a b) = -(|a|^2 + |b|^2)$, real. Also $x y = (a u - v overline(b), -a v + u b)$ and, using alternativity of $OO$ in the forms $a(a u) = a^2 u$, $(u b) overline(b) = u (b overline(b))$, $(v overline(b)) b = v(overline(b) b)$,
$ x(x y) = (-(|a|^2 + |b|^2) u + [a, v, overline(b)], thick -(|a|^2 + |b|^2) v + [a, u, b]). $
Hence $[x,x,y] = x^2 y - x(x y) = 0$ iff $[a, u, b] = 0$ and $[a, v, overline(b)] = -[a, v, b] = 0$: both components of $y$ lie in $"Ass"_OO [a,b] = {z in OO : [a,z,b] = 0}$. When $"Im" thin a$ and $"Im" thin b$ are linearly independent this kernel is the quaternion subalgebra $Q(a,b) = "span"{1, a, b, a b}$ (the associator depends only on the imaginary parts; after an orthogonalisation it is BDI Lemma 8.5, $"Ass"_OO = HH$). So: if $x$ is _non-degenerate_ (imaginary parts of $a$, $b$ independent), $u, v in Q(a,b)$ and $y in Q(a,b) times Q(a,b)$; if $y$ is non-degenerate too, symmetrically $a, b in Q(u,v)$, so $Q(a,b) = Q(u,v)$. If $y$ is degenerate (imaginary parts of $u, v$ dependent), it lies in $Q(a,b) times Q(a,b)$ anyway. If both are degenerate, the imaginary parts of $a, b, u, v$ span at most two dimensions and lie in a common $Q$. In every case $x, y in Q times Q$. $square$

*Lemma B (splitting).* _Let $Q subset OO$ be a quaternion subalgebra, $E = Q times Q$ and $E^perp = Q^perp times Q^perp$. For $x, y in E$ the operators $W_(x,y)$ and $[x, dot, y]$ preserve $E$ and $E^perp$; $E$ is the Cayley–Dickson double of $Q$, hence an octonion algebra; and for a quaternionic pair in $E$ both kernels meet $E$ in dimension exactly $4$._

$Q dot Q^perp subset Q^perp$ and $Q^perp dot Q subset Q^perp$ in $OO$, so @eq:mul gives $E dot E^perp subset E^perp$, $E^perp dot E subset E^perp$, and $E dot E subset E$. The product @eq:mul restricted to $Q times Q$ is the Cayley–Dickson double of $Q tilde.equiv HH$, i.e. $E tilde.equiv OO$. In an octonion algebra, for orthogonal imaginary $x, y$, $"Ass"[x,y] = HH(x,y)$ and $"Ass"'[x,y] = HH(x,y)^perp$ (BDI Lemma 8.5), each of dimension $4$. $square$

*Lemma C (the $E^perp$ blocks).* _Choose $e in Q^perp$ a unit and write $Q^perp = Q e$, so that $OO = Q times Q$ with @eq:mul and $E^perp = {((0,u'),(0,v')) : u', v' in Q}$. For $x = ((a,0),(b,0))$, $y = ((c,0),(d,0))$ with $a, c in "Im" thin Q$, $b, d in Q$, $⟨a,c⟩ + ⟨b,d⟩ = 0$:_
$ W_(x,y) (u', v') = (r v', thick -r u'), \
  [x, (u',v'), y] = 2 thin ((p+q) u' + (w+t) v', thick (w-t) u' + (p-q) v') = 2 M (u', v'), $
_with $r, p, q, w, t$ as in Theorem 1._

This is a direct expansion of @eq:mul at the two levels. Writing $z = (U, V)$ with $U = (0,u')$, $V = (0,v')$ one finds $x z = ((0, -a u' - overline(b) v'), (0, a v' + b u'))$ and $z y = ((0, c u' + overline(d) v'), (0, -d u' - c v'))$; multiplying out $(x z) y$ and $x (z y)$ and collecting, the coefficient of $u'$ in the first component of $W$ is $-(a c + c a) + (overline(d) b + overline(b) d) = 2 ⟨a,c⟩ + 2 ⟨b,d⟩ = 0$, the coefficient of $v'$ in the second component is likewise $0$, and the two remaining coefficients are $[overline(b), c] + [overline(d), a] = [c,b] + [a,d] = r$ and its negative. For the associator the four coefficients are $[a,c] + 2 thin "Im"(overline(d) b)$, ${overline(d), a} - {overline(b), c}$, ${a,d} - {b,c}$ and $[a,c] + 2 thin "Im"(d overline(b))$; expanding $b = b_0 + arrow(b)$, $d = d_0 + arrow(d)$ gives $2(p+q)$, $2(w+t)$, $2(w-t)$, $2(p-q)$. $square$

*Proof of Theorem 1.* (i) is Lemma A. By Lemma B, $ker W_(x,y) = (ker W_(x,y) inter E) plus.o (ker W_(x,y) inter E^perp)$, the first summand of dimension $4$, and likewise for the associator. By Lemma C the restriction to $E^perp$ is left multiplication on $Q times Q tilde.equiv HH^2$ by a $2 times 2$ quaternion matrix; left multiplication commutes with right scalar multiplication by $Q$, so each kernel is a right $Q$-subspace of $Q^2$ and has real dimension $0$, $4$ or $8$. For $W$ the matrix is $mat(0, r; -r, 0)$: kernel $Q^2$ if $r = 0$, and $0$ if $r eq.not 0$ (then $r v' = 0$ forces $v' = 0$ and $r u' = 0$ forces $u' = 0$). This is @eq:N. For the associator the matrix is $M$ and @eq:A is the statement that $dim_RR ker M = 4(2 - "rk"_HH M)$; the Study-determinant form of the rank-one condition is the usual one for $2 times 2$ quaternion matrices, $|alpha|^2 |delta|^2 + |beta|^2|gamma|^2 - 2 "Re"(overline(delta) gamma overline(alpha) beta) = |alpha|^2 |delta - gamma alpha^(-1) beta|^2$ when $alpha eq.not 0$. $square$

*Proof of the corollaries.* The value sets are read off @eq:N and @eq:A. All six combinations occur: $(4,4)$ at $(e_1 - e_2, e_3 - e_9)$; $(4,8)$ at $x = -e_2 + e_3 - e_9 + e_10$, $y = -e_1 - e_3 - e_9 - e_11$; $(4,12)$ at $(e_1, e_10)$; $(12,4)$ at $(e_1, e_2)$; $(12,8)$ at $(e_1 - e_8, e_2 - e_9)$; $(12,12)$ at $(e_1 - e_10, e_1 + e_10)$. Genericity: $r eq.not 0$ and $"rk"_HH M = 2$ are open conditions and hold at the first witness. The doubling itself is immediate: $(2N+4) + (2A-4) - 32 = 2(N+A-16)$. That BDI's Lemmas 8.7–8.10 send $(N, A)$ to $(2N+4, 2A-4)$ or $(2A-4, 2N+4)$ is their statement, checked in this convention (item (7) below); together with $delta = 0$ at Lemma 8.5 this gives Corollary 4 and the last sentence of Corollary 1. Corollary 2 is immediate. For Corollary 3, Moreno's Theorem 3.3 says that a pure $(a,b)$ with $a, b$ pure is alternative iff $a, b$ are alternative (automatic in $OO$) and linearly dependent, and his Proposition 3.1 removes the real part of $b$; together, $(a,b)$ with $a$ pure is alternative iff $[a, b] = 0$. Bilinearity gives $r = nu(x+y) - nu(x) - nu(y)$. $square$

= Remarks

*Where the basis sits.* For basis units $b, d in {0} union {plus.minus e_k}$ and $a, c in {0} union {plus.minus e_j}$ with at most one of $a, b$ and one of $c, d$ nonzero. One checks that then $"rk"_HH M in {0, 2}$ and that $dim "Ass" = 16 - dim "Ass"'$: the complement identity $"Ass" plus.o "Ass"' = SS$ used in _The Birth Function_ to write the differing clause as $2^(n+1) - 2N - 4$ is the statement $delta = 0$, and Theorem 1 shows it is a property of the defect-zero stratum, not of quaternionic pairs in general.

*What decides $"Ass"'$.* Within a fixed plane $Pi = "span"{x,y}$ the associator kernel is constant (the associator is bilinear antisymmetric in $x, y$) but $"Ass"'$ is not: in $HH(e_1, e_10)$ the pair $(e_1, e_10)$ has $dim "Ass"' = 4$ while the pair $(e_1 - e_10, e_1 + e_10)$ in the same plane has $12$. Theorem 1 locates the jump: $r$ is a _symmetric_ bilinear form on $"Im" thin E$ with values in $"Im" thin Q$, $r(z,z) = 2 nu(z)$, and $"Ass"'$ is large exactly on its isotropic pairs. Moreno's classification of alternative elements, which does not mention kernels, is therefore the kernel theory of $W$ at the sedenions.

*Positive defect.* If $delta > 0$ then $"Ass" inter "Ass"' eq.not 0$, and any nonzero $z$ in the intersection satisfies $(x z) y = 0 = x (z y)$; so $x z$ is a zero divisor or zero. Negative defect has no such reading; it is the generic case.

*What this does not do.* It does not give the birth function for quaternionic pairs of $A_5$ and beyond that are not lifts: Lemma A uses alternativity of the components, which fails in $SS$. Section 5 recovers the containment, and a block decomposition, for pairs of _alternative_ elements at every level; pairs with a non-alternative member at $m >= 5$ remain _not established_. It does not describe the Zariski strata of $"rk"_HH M = 1$ in invariant terms beyond the Study determinant. Nothing here is formalised: the Lean development of _The Birth Function_ does not contain alternativity of $A_3$, which Lemmas A and B need.

= Verification

Exact integer arithmetic (the multiplication @eq:mul by structural recursion, ranks modulo the primes $1 thin 000 thin 003$ and $1 thin 048 thin 573$, programs `defect.cpp` and `defect2.cpp`). (1) All $7 thin 413$ quaternionic pairs of weight two (signed sums of two imaginary units): Lemma A holds for every pair; @eq:N and @eq:A agree with the direct $16 times 16$ nullities for every pair; the values are $(4,4) times 4200$, $(4,12) times 924$, $(12,4) times 1827$, $(12,8) times 378$, $(12,12) times 84$. (2) $20 thin 000$ random integer pairs in $E$ for $Q = HH(e_1,e_2)$ with entries in $[-3,3]$: @eq:N and @eq:A agree in every case; values $(4,4) times 19679$, $(4,8) times 56$, $(4,12) times 5$, $(12,4) times 233$, $(12,8) times 26$, $(12,12) times 1$ -- the combination $(4,8)$, absent at weight two, appears. (3) $60 thin 000$ further pairs: $dim ker M = 8$ exactly when $p = q = w = t = 0$. (4) The octonion fact of Lemma A, $dim "Ass"_OO [a,b] = 4$ for independent imaginary parts: $3000 \/ 3000$ random pairs. (5) Moreno's criterion in the convention @eq:mul: alternative iff $[a,b] = 0$, $4000 \/ 4000$ random imaginary elements, $2007$ of them alternative. (6) Inside the coordinate quaternion $HH(e_1, e_10)$, with $e_1 in OO$ and $e_10, e_11 in OO ell$: of the $546$ primitive integer orthogonal pairs with entries in $[-3,3]$, $500$ have $(4,4)$, $36$ have $(4,12)$ (the plane contains $e_1$), $8$ have $(12,4)$ (both in the upper plane), $2$ have $(12,12)$ (the plane contains $e_1$ and the pair is symmetric about it) -- exactly the strata $r = 0$ and $"rk"_HH M$ predict. (7) Corollary 4's lift rule, $(N,A) arrow.bar (2N+4, 2A-4)$ for same-side and $(2A-4, 2N+4)$ for cross lifts: the six witness pairs and $400$ random quaternionic pairs of $E$, all four lifts each, $406 \/ 406$; every lift is again a quaternionic pair (program `lifts-check.cpp`). (8) Lemma D: $"alternative"(x) <=> "(I)" and "(II)"$ on $150$ elements of $A_5$ and $150$ of $A_6$ drawn from three families (both conditions true; (I) true and (II) false; (II) true and (I) false), $300 \/ 300$; property (N), $dim {b : [a, u, b] = 0} = 2$, for $1000$ dense and $1008$ sparse pure $a$ in $A_4$, $300 + 329$ in $A_5$, $60 + 123$ in $A_6$ (program `nucleus-check.cpp`). (9) The identity $[u, b, b] = -[b, b, u]$ cited in Lemma D, and flexibility $[b, u, b] = 0$: $400 \/ 400$ random elements in each of $A_3, A_4, A_5$.

*Status.* ESTABLISHED (hand proof, exact computational check on every step): Theorem 1 and Corollaries 1–3. Corollary 4: the doubling identity is proved here; the lift map is BDI's, checked in this convention on $406$ pairs. The literature read for this note is BDI #cite(<bissDuggerIsaksen2008>) and Moreno #cite(<moreno2004alt>); later work on sedenion zero divisors was not searched, and the word "new" is withheld until it is.

= The tower: all levels, for pairs of alternative elements

Lemma A does not survive the sedenions as stated, because its proof uses alternativity of the components. For the class of pairs that BDI's Section 11 is about -- quaternionic pairs of _alternative_ elements -- Moreno's classification supplies the containment at every level, and with it a decomposition of both kernels along a tower of doubled subalgebras.

*Lemma D (alternative elements in the convention @eq:mul).* _Let $n >= 3$ and $x = (a, b) in A_(n+1)$ with $a in "Im" thin A_n$, $b in A_n$. Then $x$ is alternative iff_
$ "(I)" quad [a, u, b] = 0 quad "and" quad "(II)" quad [a, a, u] + [b, b, u] = 0 quad "for all" u in A_n . $
_Suppose moreover that $A_n$ satisfies_ (N): _for every nonzero pure $a$, ${b : [a, u, b] = 0 "for all" u} = RR plus.o RR a$. Then $x$ is alternative iff either $a != 0$ is alternative and $b in RR plus.o RR a$, or $a = 0$ and $"Im" thin b$ is alternative. Property_ (N) _holds at $n = 3$ (BDI Lemma 8.5), at $n = 4$ by Theorem 1, and for every $n >= 4$ it is Moreno's Theorem 2.3_ #cite(<moreno2004alt>).

$x^2 = -(|a|^2 + |b|^2)$ is real. For $z = (u, v)$ the raw expansion in the proof of Lemma A -- before alternativity of $OO$ was used -- is $x(x z) = (a(a u) - (u b) overline(b) + [a, v, overline(b)], thick a(a v) - (v overline(b)) b + [a, u, b])$. So $[x, x, z] = 0$ for all $z$ iff, separating $u$ and $v$: $[a, v, overline(b)] = 0$ and $[a, u, b] = 0$ for all $u, v$, and $a(a u) - (u b) overline(b) = -|x|^2 u$, $a(a v) - (v overline(b)) b = -|x|^2 v$. Since $overline(b) = 2 b_0 - b$ and the associator kills real entries, the first-order conditions are (I). With $a^2 = -|a|^2$, $b overline(b) = |b|^2$ and flexibility of Cayley–Dickson algebras ($[u, b, b] = -[b, b, u]$; Moreno, Section 1), $a(a u) + |a|^2 u = -[a, a, u]$ and $(u b) overline(b) - |b|^2 u = [u, b, overline(b)] = -[u, b, b] = [b, b, u]$, so the second-order conditions are (II). Given (N): if $a != 0$, (I) gives $b = s + t a$ and (II) becomes $(1 + t^2)[a, a, u] = 0$; if $a = 0$, (II) is $[b, b, u] = 0$. Conversely both families satisfy (I) ($[a, u, a] = 0$ by flexibility) and (II). For (N) at $n = 4$: let $a != 0$ be pure in $SS$ and $[a, u, b] = 0$ for all $u$; put $b' = "Im" thin b - (⟨"Im" thin b, a⟩ \/ |a|^2) a$, so $[a, u, b'] = 0$ for all $u$. If $b' != 0$ then $(a, b')$ is a pair of nonzero orthogonal imaginary elements with $[a, a, b'] = 0$ ($u = a$) and $[b', b', a] = -[a, b', b'] = 0$ ($u = b'$): a quaternionic pair with $"Ass"[a, b'] = SS$, of dimension $16$, contradicting the bound $12$ of Theorem 1 (iii). Hence $b' = 0$. $square$

#thm("Theorem 2", [tower decomposition])[Let $m >= 3$ and let $(x,y)$ be a quaternionic pair of alternative elements of $A_m$. Then:

(i) there is a quaternion subalgebra $Q subset OO = A_3$ such that $x, y in E_m := Q^(2^(m-3))$, the $(m-3)$-fold Cayley–Dickson double of $Q$ inside $A_m$ (all $2^(m-3)$ octonion coordinates of $x$ and $y$ lie in $Q$); $E_m$ is a subalgebra isomorphic to $A_(m-1)$;

(ii) $E_m^perp = (Q^perp)^(2^(m-3))$ is invariant under $W_(x,y)$ and $[x, dot, y]$, so
$ dim "Ass"'_(A_m)[x,y] = dim "Ass"'_(E_m)[x,y] + beta_m, quad dim "Ass"_(A_m)[x,y] = dim "Ass"_(E_m)[x,y] + alpha_m, $
where $beta_m, alpha_m$ are the kernel dimensions of the restrictions to $E_m^perp$; both restrictions commute with the right action of $Q$ on $(Q^perp)^(2^(m-3)) tilde.equiv HH^(2^(m-3))$, so $alpha_m, beta_m in 4 ZZ$, $0 <= alpha_m, beta_m <= 2^(m-1)$;

(iii) under an isomorphism $E_m tilde.equiv A_(m-1)$ the pair stays a quaternionic pair of alternative elements, so (i)–(ii) iterate down to $E_4 tilde.equiv A_3 = OO$, where $"Ass"' = HH(x,y)^perp$ and $"Ass" = HH(x,y)$ (BDI Lemma 8.5): with $beta_k, alpha_k$ the kernels of the restrictions to the complement of $E_k$ in $A_k$ (dimension $2^(k-1)$), transported along the isomorphisms,
$ dim "Ass"'[x,y] = 4 + sum_(k=4)^m beta_k, quad dim "Ass"[x,y] = 4 + sum_(k=4)^m alpha_k . $
At $k = 4$, $beta_4 = 8 dot bb(1)[r = 0]$ and $alpha_4 = 4(2 - "rk"_HH M)$ by Theorem 1.]

*Proof.* By Lemma D -- equivalently Moreno #cite(<moreno2004alt>), Theorem 3.3 with Proposition 3.1 -- for $n >= 3$ a pure element of $A_(n+1)$ is alternative iff it has the form $(p, s + t p)$ with $p$ a pure alternative element of $A_n$ and $s, t in RR$, or the form $(0, s + p)$. For $n = 3, 4$ this is proved above from BDI Lemma 8.5 and Theorem 1; for $n >= 5$ it imports property (N) from Moreno's Theorem 2.3. Hence an alternative $x in A_m$ lies in $C_p times C_p$ with $C_p = "span"{1, p}$, and $y$ in $C_(p') times C_(p')$; both lie in $B times B$ for any subalgebra $B subset A_(m-1)$ containing $p, p'$. Now $p, p'$ are themselves pure alternative elements of $A_(m-1)$, so they lie in $C_(p_1) times C_(p_1)$ and $C_(p_1') times C_(p_1')$ for pure alternative $p_1, p_1' in A_(m-2)$, and $B$ may be taken of the form $B_1 times B_1$ with $B_1 in.rev p_1, p_1'$. Descending to $A_3 = OO$, where every element is alternative, we reach $p_*, p_*' in "Im" thin OO$ and may take $B_* = Q$, any quaternion subalgebra containing them. Unwinding, $x, y in Q^(2^(m-3)) = E_m$, which is the iterated Cayley–Dickson double of $Q$ by @eq:mul applied coordinatewise, hence a subalgebra isomorphic to $A_(m-1)$. This is (i). For (ii): $Q dot Q^perp subset Q^perp$ and $Q^perp dot Q subset Q^perp$ in $OO$, and @eq:mul only ever multiplies coordinates, so $E_m dot E_m^perp subset E_m^perp$ and $E_m^perp dot E_m subset E_m^perp$; the restriction of $W_(x,y)$ to $E_m^perp$ is built from left and right multiplications by elements of $E_m$, which act on each $Q^perp$-coordinate by left multiplications by elements of $Q$ (after the identification $Q^perp = Q e$ with $e perp Q$ a unit, as in Lemma C), and these commute with right multiplication by $Q$. (iii) is immediate from (i)–(ii) and Theorem 1. $square$

#thm("Corollary 5", [the bin digits are blocks])[For a pair of basis units of $A_m$, $m >= 5$, define $epsilon_k in {0,1}$ by $"birth"(a,b) = 4 + sum_(k=4)^m 2^(k-1) epsilon_k$ -- the binary digits of the bin index $("birth" - 4) \/ 8$ of _The Birth Function_, Theorem 4. At $m = 5$, for all $465$ pairs, $beta_k = 2^(k-1) epsilon_k$ and $alpha_k = 2^(k-1)(1 - epsilon_k)$, $k = 4, 5$: each block of the tower is either $0$ or the whole complement, and the digit of the bin index at position $k$ records which. OBSERVED at $m = 5$ (exhaustive); the paper's bin dynamics -- "append $1$" for an agreeing lift, "complement, then append $0$" for a differing one -- is then a statement about the top block, not established here for general $m$.]

*What is observed at level 5 beyond the basis.* On $4002$ random quaternionic pairs of alternative elements of $A_5$ (Moreno's parametrisation, integer parameters in $[-2,2]$; programs `a5.cpp`, `a5block.cpp`): containment in $Q^4$, invariance of $E_5^perp$ and additivity of both kernels hold in every case. The values seen there: $(dim "Ass"', dim "Ass") = (4,4)$ for $3215$ pairs, $(12,4)$ for $481$, $(28,4)$ for $300$, $(4,12)$ for $4$, $(12,12)$ for $1$, $(4,28)$ for $1$, with $beta_5 in {0, 8, 16}$. That sample missed a stratum. The generic pair at level $5$ still has $(4,4)$, defect $-24$.

#thm("Proposition 6", [the mod-8 law stops at the sedenions])[Theorem 2 gives $beta_m in 4 ZZ$. The stronger congruence $beta_m in 8 ZZ$, and with it $dim "Ass"' equiv 4 (mod 8)$ for every quaternionic pair of alternative elements, is false at $m = 5$. The elements
$ x = e_3 - e_(16) - 2 e_(19), quad y = e_2 - e_3 - 2 e_(10) + 2 e_(11) - e_(16) $
of $A_5$ are alternative, orthogonal and anticommute, and
$ dim "Ass"'[x,y] = 8, quad dim "Ass"[x,y] = 4, quad beta_5 = 4. $
The $4$ in the top block is the kernel of a $2 times 2$ Hermitian matrix over $HH$ of Study determinant zero and not itself zero; right $HH$-linearity accounts for the factor $4$ and does not double it.]

*Proof.* Alternativity, orthogonality and the anticommutator are finite checks in the product @eq:mul. The three dimensions are the nullities of integer matrices --- $W_(x,y)$ and the associator on the standard basis of $A_5$, and the restriction of $W_(x,y)$ to the complement of $E_5 = HH(e_1, e_2)^4$, with basis $e_4, dots, e_7, e_(12), dots, e_(15)$ and its top double --- computed by Gaussian elimination modulo $1 thin 000 thin 003$ and modulo $1 thin 048 thin 573$, which agree (program `mod8-fail.cpp`). The Hermitian description is the shape of that restriction, in the notation of Theorem 3 below: $p = -4 e_1$, $a = c = 4 e_1$, $b = 8$, so $P = [[0, -4e_1], [4e_1, 0]]$ and $B = [[4 e_1, 8], [-8, 4 e_1]]$; $P$ is invertible with $P^2 = 16$, and the Schur complement $S = P + B P^(-1) B$ equals $-16 [[1, -e_1], [e_1, 1]]$, whose kernel is ${(e_1 g, g) : g in HH}$, a right $HH$-line, of real dimension $4$. $square$

#thm("Proposition 7", [the top block at level 5])[Let $(x,y)$ be a quaternionic pair of alternative elements of $A_5$. Then $beta_5 in {0, 4, 8, 16}$. All four values occur. In particular $12$ does not.]

*Proof.* By Theorem 2 the pair lies in $E = Q^4$ for some quaternion subalgebra $Q subset OO$. An automorphism of $OO$ carries $Q$ to $HH(e_1, e_2)$ and extends to $A_5$ by acting on each octonion coordinate; it preserves $W$ and the top doubling, so it is enough to treat $E = "span"{e_i : i in {0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27}}$. On the complement $F times F$, with $F tilde.equiv HH^2$, the operator $W_(x,y)$ is the anticommutator of the two $4 times 4$ matrices over $HH$ that the doubling formula assigns to left multiplication by $x$ and right multiplication by $y$ (the identity is bilinear, and it holds on all $256$ pairs of basis elements of $E$). For an orthogonal pair with no component along $1$, that anticommutator has the shape $[[P, B], [-B, P]]$ with $P = [[0, p], [-p, 0]]$, the operator of Theorem 3: the shape holds on every pair of distinct imaginary basis elements, and on each square $e_i^2$ the failure is exactly $2 I$, which cancels against $⟨x, y⟩ = 0$. If $p != 0$ then $P$ is invertible and the kernel is the kernel of a single $2 times 2$ matrix over $HH$, hence of real dimension $0$, $4$ or $8$. If $p = 0$ the kernel is a square of the kernel of the off-diagonal block, hence of real dimension $0$, $8$ or $16$. The four values occur: $0$, $8$ and $16$ in the level-$5$ census, and $4$ by Proposition 6. $square$

= Level 5 closed

By Theorem 2 and the $G_2$ reduction of Proposition 7 we may take $Q = HH(e_1, e_2)$, so $E_5$ is spanned by the units $e_i$ with $i in.not {4,5,6,7} + 8 ZZ$ and $F = Q^perp times Q^perp = "span"{e_4, dots, e_7, e_(12), dots, e_(15)}$; the complement of $E_5$ in $A_5$ is $F times F$. Identify each copy of $Q^perp$ with $HH$ by $e_(4+i) arrow.l.r e_i$ ($i = 0,1,2,3$), so $Q^perp$ is a right $Q$-module and the operators below are $2 times 2$ matrices over $HH$ acting on columns by left multiplication of the entries. By Moreno's parametrisation an alternative pure element of $A_5$ lying in $E_5$ is
$ x = (alpha, thick s + t alpha), quad alpha = (X_0, thick sigma + tau X_0), quad X_0 in "Im" thin Q, quad s, t, sigma, tau in RR, $
and likewise $y$ with $Y_0, s', t', sigma', tau'$. Write $[u,v] = u v - v u$ and $⟨u, v⟩$ for the inner product of imaginary quaternions.

#thm("Theorem 3", [the top block at level 5, closed form])[Let $(x, y)$ be a quaternionic pair of alternative elements of $A_5$ in the normal form above. Then:

(i) $dim "Ass"'_(E_5)[x,y] in {4, 12}$, and it is $12$ exactly when $t = t'$ or $alpha$ and $alpha'$ are parallel.

(ii) On $F times F$, $W_(x,y)(f, g) = (P f + B g, thick -B f + P g)$ with
$ P = mat(0, p; -p, 0), quad B = mat(a, b; -overline(b), c), $
$ p = (1 + t t')(tau' - tau) [X_0, Y_0], quad b = (t' - t) (2 (tau' - tau) ⟨X_0, Y_0⟩ + 2 sigma' X_0 - 2 sigma Y_0), $
$ a = (t' - t) ((1 + tau tau') [X_0, Y_0] + 2 (sigma' tau X_0 - sigma tau' Y_0)), $
$ c = (t' - t) ((1 + tau tau') [X_0, Y_0] - 2 (sigma' tau X_0 - sigma tau' Y_0)). $

(iii) $beta_5 = dim_RR ker (P + B P^(-1) B) in {0, 4, 8}$ if $p != 0$, and $beta_5 = 2 dim_RR ker B in {0, 8, 16}$ if $p = 0$.

(iv) If $dim "Ass"'_(E_5)[x,y] = 12$ then $B = 0$ and $beta_5 = 16 dot bb(1)[p = 0]$; for parallel $alpha, alpha'$ this gives $beta_5 = 16$.

(v) Consequently $dim "Ass"'[x, y] in {4, 8, 12, 20, 28}$. All five values occur; $16$ and $24$ do not.]

*Proof.* (i) is Theorem 1 inside $E_5 tilde.equiv A_4$: the pair is $(alpha, s + t alpha), (alpha', s' + t' alpha')$ with $alpha, alpha'$ pure in the octonion algebra $E_4 = Q times Q$, so $r = [alpha', s + t alpha] + [alpha, s' + t' alpha'] = (t - t') [alpha', alpha]$, which vanishes iff $t = t'$ or $[alpha, alpha'] = 0$, and two pure octonions commute iff they are parallel.

(ii) The map $(x, y) arrow.bar W_(x,y)|_(F times F)$ is bilinear, and so are the right-hand sides once $x, y$ are written in the sixteen $Q$-coordinates $(X_0, X_1, X_2, X_3)$, $(Y_0, dots, Y_3)$ of $E_5 = Q^4$: there
$ p = [X_0, Y_1] - [X_1, Y_0] + [X_2, Y_3] - [X_3, Y_2], $
$ a, c = K plus.minus J, quad K = [X_0, Y_2] + [X_1, Y_3] - [X_2, Y_0] - [X_3, Y_1], $
$ J = (X_1 overline(Y_3) - overline(X_1) Y_3) - (X_3 overline(Y_1) - overline(X_3) Y_1), $
$ b = [X_0, Y_3] - [X_1, Y_2] - [X_2, Y_1] + [X_3, Y_0] \
 quad + 2 X_0 overline(Y_3) - X_2 overline(Y_1) - overline(X_1) Y_2 + 2 overline(X_3) Y_0 + overline(X_1) thin overline(Y_2) + overline(X_2) thin overline(Y_1), $
and the lower-left entry of $B$ is $-overline(b)$. A bilinear identity holds iff it holds on pairs of basis vectors; the block shape, the left-multiplication form of every block, and these four formulas were checked on all $15 times 15$ pairs of imaginary basis units of $E_5$ (program `level5-closed.cpp`; on the diagonal pairs $e_i, e_i$ the shape fails by exactly $2 I$ in $P$, which is cancelled by $⟨x, y⟩ = 0$, as in Proposition 7). Substituting $X_1 = sigma + tau X_0$, $X_2 = s + t X_0$, $X_3 = t X_1$ and the primed analogues gives the displayed forms: the commutators reduce by $[X_1, Y_1] = tau tau' [X_0, Y_0]$ and $[X_0, Y_1] = tau' [X_0, Y_0]$; the identity $u overline(v) - overline(u) v = 2 ("Re" thin v dot "Im" thin u - "Re" thin u dot "Im" thin v)$ gives $J$; and $X_0 Y_0 + Y_0 X_0 = -2 ⟨X_0, Y_0⟩$ gives $b$. (Checked on $6000$ further pairs -- `level5-closed.cpp` with argument $6000$ -- as were (i), (iv), additivity, and the value of $beta_5$ by direct nullity.)

(iii) $P^2 = |p|^2 I$ since $p$ is a commutator, hence pure. If $p != 0$, the kernel equations $P f + B g = 0 = -B f + P g$ give $f = -P^(-1) B g$ and then $(P + B P^(-1) B) g = 0$; the kernel is the graph of $-P^(-1) B$ over $ker(P + B P^(-1) B)$, a right $HH$-submodule of $HH^2$. (The order matters: $P + P^(-1) B P B$ has a different kernel unless $P$ and $B$ commute, and gives $0$ on the pair of Proposition 6; program `schur-check.cpp` confirms $dim ker(P + B P^(-1) B)$ against the direct nullity on that pair and on $14 thin 120$ random pairs with $p != 0$.) If $p = 0$ the equations decouple into $B g = 0 = B f$.

(iv) If $t = t'$, every entry of $B$ carries the factor $t' - t$. If $alpha' = lambda alpha$ then $Y_0 = lambda X_0$, $sigma' = lambda sigma$, $tau' = tau$, so $[X_0, Y_0] = 0$ and $sigma' tau X_0 - sigma tau' Y_0 = 0$, whence $p = a = b = c = 0$. With $B = 0$ the operator is $P plus.o P$, invertible if $p != 0$ and zero if $p = 0$.

(v) From (i), (iii), (iv): if $dim "Ass"'_(E_5) = 12$ the total is $12$ or $28$; if it is $4$ the total is $4 + beta_5 in {4, 8, 12, 20}$. Realisations: $4$ is generic; $8$ is Proposition 6; $12$ occurs both as $12 + 0$ and as $4 + 8$; $20$ and $28$ occur on the basis ($84$ and $171$ pairs, Corollary 5). $square$

*Remark.* Formulas (ii) and statements (iii)–(iv) do not use alternativity: they hold for every orthogonal imaginary pair of $E_5 = Q^4$ (checked on $6000$ such pairs with arbitrary $X_1, Y_1$). Among those, $(dim "Ass"'_(E_5), beta_5) = (4, 16)$ occurs -- for instance $x = -3 e_1 + 2 e_3 - 2 e_9 - 3 e_(11) + 3 e_(17) - 2 e_(19) + 2 e_(25) + 3 e_(27)$, $y = -2 e_1 - 2 e_9 - e_(11) + 2 e_(16) - 2 e_(17) - 2 e_(25) - e_(27)$, with $dim "Ass"' = 20$, $dim "Ass" = 12$, neither element alternative. What alternativity buys is Theorem 2's containment, not the block algebra.

*Observed at levels 6 and 7* (program `tower-close.cpp`, Moreno's parametrisation iterated, integer parameters in $[-2, 2]$, standard $Q$). Level $6$, $2000$ pairs: invariance of $E_6^perp$, additivity of both kernels, and the block shape $W(f,g) = (P f + B g, -B f + P g)$ on the top complement ($P, B$ now $4 times 4$ over $HH$) hold in every case; $beta_6 in {0, 8, 16, 32}$ ($1801, 8, 33, 158$), $alpha_6 in {0, 8, 16, 32}$; $(dim "Ass"'_(E_6), beta_6) = (12, 8)$ occurs, so $dim "Ass"' = 20$ arises at level $6$ with a quarter block ($8$ of $32$). Level $7$, $400$ pairs: same structural checks all pass; $beta_7 in {0, 32, 64}$, $alpha_7 = 0$ throughout. The associator does not have the $W$ shape on the top complement once $s$ or $s'$ is nonzero (the pairs involving the unit $(0, 1)$ break it), so no analogue of Theorem 3 for $alpha_k$ is offered here.

*Status.* Theorem 2 (i)–(iii): ESTABLISHED. At $m = 5$ it is self-contained (Lemma D with property (N) from BDI Lemma 8.5 and Theorem 1); for $m >= 6$ the single import is Moreno's Theorem 2.3 at $n >= 5$, an isomorphism-invariant statement checked in our convention on $812$ elements of $A_5$ and $A_6$ (OBSERVED there, proved in his). Checked exhaustively at level $5$ on the basis and on $4002$ random pairs. Corollary 5: OBSERVED at $m = 5$, on the basis. Proposition 6: ESTABLISHED. Proposition 7: ESTABLISHED. Theorem 3: ESTABLISHED (bilinear identities proved on the basis of $"Im" thin E_5$, the rest by hand; everything re-checked on $6000$ random alternative pairs), so $beta_5$ is explicit and the value set of $dim "Ass"'$ at level $5$ is closed. Levels $6$ and $7$: the block shape and $beta_k in 4 ZZ$ are theorems (Theorem 2), the value sets are OBSERVED only. The explicit form of $beta_k$ for $k >= 6$ and of $alpha_k$ for $k >= 5$: NOT ESTABLISHED. Quaternionic pairs with a non-alternative member at levels $>= 5$: not treated beyond the Remark.

#bibliography("birth-function-refs.yml", style: "ieee")
