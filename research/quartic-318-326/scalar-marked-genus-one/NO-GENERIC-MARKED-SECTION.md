# No generic beta section on the exact cut

Scope: function-field results for the auxiliary E_c. This is not
an obstruction to any particular rational c, and it is not a rank
or rationality result for the original E_n or the original pole.

Fix nonsquare β>1, constant. Use D=βc², δ=1−D, and
`E_c : y²=x(x²+β(82D−18)x+81β²δ²)`. The explicit point
P=(9βδ,(9βδ)(8βc)) has order four and x-class βδ.

## Over the rational parameter line

The discriminant is a nonzero constant times
`D(25D−9)(1−D)^4`. As a polynomial in c it has degree
12. The c4 is a unit at each finite bad geometric point.
Thus, by [Tate's original algorithm](https://wstein.org/Tables/antwerp/tate/tate.pdf),
the geometric multiplicative fibres are two I4 at D=1,
two I1 at D=9/25, and one I2 at c=0. The minimal model
has good reduction at ∞, with coefficient scalings c⁻²,c⁻⁴.
The complex elliptic surface over P¹ has e=12 and b2=10.
Shioda–Tate (see [Shioda, On the Mordell–Weil lattices](https://rikkyo.repo.nii.ac.jp/record/10027/files/AA00610867_39-02_05.pdf)
and [Schütt–Shioda, §6.10 and Cor. 6.13](https://arxiv.org/pdf/0907.0298#page=29))
bounds geometric Mordell–Weil rank by
10−[2+2(4−1)+(2−1)]=1.

Take k=3/5 in the exact even quartic of the cut. It gives
H=3√β(D+16/25), hence the section

    S = (81β/25, (81β√β/5)(D+16/25)).

This is not a torsion section. At the c=0 fibre extend to
Q(√β) and divide x by β, y by β√β. Its nonsingular point
on y²=x(x−9)² is (81/25,1296/125). In that split nodal
cubic the normalization coordinate T=y/(x−9)=−9/5 gives
the smooth group torus coordinate (T−3)/(T+3)=−4
(up to inversion). It is not a root of unity; reduction
into the smooth Néron torus is a group homomorphism.
Thus the geometric rank is one. Constant conjugation
√β↦−√β sends S to −S, so the rational parameter line
Q(c) has free rank zero.

Torsion over Q(c) has order at most four: specialize at
c=0 into the Néron fibre, whose geometric component group
has order 2 and whose identity component is the nonsplit
norm-one torus of the real quadratic Q(√β)/Q. Its rational
torsion is contained in ±1. The kernel in the formal group
has no torsion in residue characteristic zero: the linear
term m in [m] is a unit, so a nonzero parameter of positive
valuation cannot be killed by [m]. Thus the literal order
four P exhausts all rational parameter-line points.
Their x-classes are 1 and βδ (the Kummer value at (0,0)
is the square 81β²δ²). Neither equals β in Q(c)×/squares:
β is nonsquare constant and δ has simple geometric roots.

## Fixed theta, the rational-base conic

Fix a positive nonsquare θ disjoint from β. If a real
prepared datum exists, its instance c,e supplies a rational
point of the smooth conic βc²+θe²=1, hence the base is rational.
Its function field is Q(c)(√(δ/θ)). The constant field is Q
because the conic is geometrically integral.

For geometric rank use the degree-two cover w²=δ first
(θ=1): its branch is at the two I4 fibres, doubled into two
I8 fibres. The I2 has two unramified lifts; the two I1 fibres
have four unramified lifts. The elliptic surface has base
genus zero and Euler number 24. By the canonical bundle/
Hodge formula it is K3 (or just use h11=20 for the rank
bound). Its trivial lattice has rank
2+2(8−1)+2(2−1)=18, so its geometric free rank is at most 2.
The invariant rank for the deck switch w↦−w is the
parameter-line rank 1 already proved. The anti-invariant
free space has dimension at most one. The fixed-θ conic
is the constant quadratic twist of this cover; its deck
anti-invariant module therefore gets multiplied by the
constant character χ_θ, while the invariant module is unchanged.
Since the invariant rational rank is zero, at most a single
nontrivial θ can gain a generic rational section, even
without identifying whether the anti-space is nonzero.

For actual a=0 one can exclude *all* nontrivial admissible
θ from that last possibility by inertia, as follows. For an
odd p≥7 with p∤β the θ=1 cover surface above has smooth
proper good reduction after a finite unramified extension
of Q_p. Indeed the conic w²+βc²=1 is smooth over Z_p and
its ramification and singular fibre positions remain
disjoint; over an unramified extension they are sections
with D=0, 1, 9/25 as above (with the indicated lifts).
The same discriminant/c4 calculations are units where
required, including the good points over c=∞. The
expected bad fibres are therefore relatively nodal with
the same multiplicities m=8,2,1.

Here is the local simultaneous-resolution justification.
After unramified splitting of slope units, near a nodal
point choose the lifted critical root of the cubic:
its second derivative is a unit, so it lifts étale-locally.
Writing the polynomial as f(x₀)+(x−x₀)² times a unit
allows an étale square root of that unit. The product
of the two node parameters is then f(x₀). The other
critical value is a unit and the cubic resultant gives
f(x₀) equal to the local base parameter to power m
times a unit. Absorb the unit to obtain uv=r^m, over
the unramified DVR. This permits an identical relative
desingularization in both characteristics: blow up the
relative singular section u=v=r=0, whose u- and v-charts
are smooth; the r-chart has equation ab=r^(m−2).
Repeat at its singular section until m≤1 (m=0 gives
ab=1). These blow-ups are proper and glue along the
disjoint fibre centres. Thus the smooth model is
simultaneous, not merely a numerical claim from Euler
characteristics. Smooth proper base change makes inertia
trivial on étale H²(1); the cycle map for Néron–Severi
and its quotient by the trivial lattice give the same
on the geometric Mordell–Weil free module, in particular
on the potential one-dimensional anti-space.

Actual a=0 β is divisible by 5. Every nontrivial θ from
the same Prepared cut is squarefree and coprime to 6β,
so some p≥7 dividing θ is a good inertia prime above.
Its character χ_θ is ramified there, unlike the anti-space.
Thus the twisted anti-space has no invariant rank.
Torsion again has order at most four by the same c=0
specialization: the conic place has residue Q(√θ), the
norm-one splitting field Q(√θ,√β) is real, β remains
nonsquare in Q(√θ), and the I2-component group is at
most 2. P is still order four, but its x-class now is
βθ. It is distinct from β in the conic function field
because θ stays nonsquare in a regular function field.

Conclusion: on the **generic fixed-theta norm conic** for
a=0 and θ>1, the only points are the four torsion points,
and there is no beta-marked section. When θ=1, the order
four point has the beta class (no assertion about selected
opens). None of these generic results bounds ranks on any
individual arithmetic fibre; a special actual c can still
acquire a beta point or fail by Sha. No actual h or θ value
has been computed here.
