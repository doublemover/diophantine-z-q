# Independent review of two sufficient point certificates on the same scalar

**Exact mathematical and replay PASS, 2026-11-21.** Bindings:

- Genus one: author manifest b8016ad8761b5db9c39997fc600a3b6aee36b500e666f1d92096237e089b35eb and paper 00b543f85732b0f09fecf2137c056e8f161590a1357054273ff8467fac4fed01.
- Genus nine: author manifest 8cac182a0cdf5bc87dd730efea6b9f1e5c95b05722c56419abd67ae99a573850 and paper c946e005c90b956dcbf846f3eb7ce18ab782de824766286fcb0fc392fa652a0f.

I authenticated the two manifests against their own and upstream bytes and
reran both exact author checkers. Both target the unchanged compact
a=0, h=473592745039516333133760 and its literal positive nonsquare δ,
not a substituted slope or squarefree truncation. Each gives the original
PointPair, with both ordinates nonzero, **if** its own curve has a rational
point. They are sufficient alternatives, not equivalent point searches.

**Genus one.** The translated ordinates and the stated squares give the raw
identity directly: the square of W is
16 β⁴ δ (4q−1)²/[5q²(q+1)]. The order of [β], [5], [5β]
is the root order (0,4βδ,−βδ), as seen directly from the three
coordinate squares. The three nonidentity even-sign flips are
fixed-point-free, also at infinity, so the degree-four quotient is the
geometric [2] map. Independently, in the scaled variables
(a,b,z)=(Aδ/β,Bδ,uδ), the determinant pencil of
b²−βa²=δT² and z²−5b²=−δT² is βδ t(t−5)(t−1),
confirming the same Jacobian. The mark is not rational torsion:
no rational root has that first class and no root has a rational half.
The base model indeed becomes y²=x³−7x−6 and its exact bad-prime
data have root number +1 at 2 and split multiplicative reduction at 5
([40.a2 local data](https://www.lmfdb.org/EllipticCurve/Q/40/a/2)).
The actual positive twist is square at 2, has v₅=1, and the odd
good primes' signs multiply to +1. The ramified Steinberg sign at 5
is also +1, so the global sign is −1. It does not compute rank.

For the same curve, square δ gives an explicit smooth local seed;
even depth elsewhere gives a unit twist of a smooth genus-one
reduction. At odd depth the Ready guards force β to be a local square,
so the two equations are soluble precisely when 5 is square there.
This is exactly the literal Q(√5)-norm test on δ. It has **not**
been passed: the four published odd-depth primes split, but their
product is 5 mod 8 whereas the actual positive squarefree θ is 1 mod 8.
Hence some further odd-depth support exists.

**Genus nine.** The signed translation changes the ordinate ratio by
((z₂−1)/(z−1))² exactly; dividing the corresponding cubic identity gives
the original raw W²=δ f(t)f(t′). The useful real region is 0<q<1/4.
None of its excluded boundary points can yield a rational point
on the cover. The two branch sets have eight points each with four
shared, giving twelve geometric branch points, each of inertia two.
Riemann–Hurwitz gives genus nine. Outside {2,3,5,13} and the two
scalar supports the branch points stay distinct; the relative local
double covers give good reduction.

At q=1/4 the ratio F/G tends to the square 64; at q=−3/4 the
product FG tends to the square 9/64. A local inverse function at
the simple zero provides a nonzero square while maintaining the
specified q-class. This works in the punctured disk even at 2.
At odd δ-depth the local square β and q near zero suffice, with no
additional restriction on which odd-depth primes occur. For the
remaining large unit places, Hasse–Weil and smooth lifting suffice.
I independently rebuilt the complete set of fifteen small exceptional
unit-class rows by testing membership in actual square sets and
verified every supplied useful-open witness, including p=13. Thus
this curve is everywhere locally soluble without the genus-one
norm premise. Neither local solubility, underlying torsor parity,
nor either multisection gives an arithmetic rational point on the
original scalar. No Lean compilation or remote write.

Reviewed by the independent proof/CI lane.
