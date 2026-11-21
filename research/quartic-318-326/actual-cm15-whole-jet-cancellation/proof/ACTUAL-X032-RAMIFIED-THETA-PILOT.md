# Whole ramified theta coefficients on a true prime ray: X₀(32), p=5

This is a genuine finite modular pilot for the new *whole* coefficient
algorithm, not an evaluation for the selected lower level N=205042530.
It changes the level, auxiliary and ray **only for calibration**. A
positive seed and a genuine cancellation occur on the same pilot ray.

Fix the pointed map in 1b2ade9e from X₀(32): Y²=X³+4X to
E:y²=x³−x. For any prime q≡1 mod 8, q>5, take the fundamental
Δ=−15q, K=Q(√Δ), conductor-one cyclic 32-mark and genus character
ψ=χ_{−3}∘Nm. The real genus twist is 5q. Call q=1 the already
proved seed, not a prime. The two exact orientations select (1+√Δ)/2
on C₃₂ by either root of X²−X+(1−Δ)/4 modulo 32. The associated
ramified 5-ideal has genus value (−3/5)=−1. Its square is principal
and the ideal itself is not: a nonrational principal generator
must have norm at least |Δ|/4, which exceeds 5 for q>5;
for q=1, x²+15y²=20 has no solutions and a rational generator
has square norm. Thus the geometric Frobenius gives actual pairs.

## 1. One proved maximal order and two genuine torsion frames

All geometric supersingular marked labels are on B:y²=x³+1 over F₂₅,
with B[2] visible and cyclic C₃₂ classified by actual nonbacktracking
degree-two chains. The checked donor a7bbedad supplies its 16 distinct
marked labels, their actual ordered kernel chains and their q-normalized
f₃₂ values in the differential dx/(2y) of this one B. We do not replace
these values by an eigenvector or list of j-invariants.

Write ρ²=2, ζ=(-1+ρ)/2 in F₂₅, ω(x,y)=(ζx,y), and Π=Frob₅.
Then Π²=[−5] (the direct point count is 6), Πω=ω²Π, and J=1+2ω
has degree 3 and kernel x=0,y=±1. Those points are F₅-rational,
so Π−1 factors on the right through J. Its actual integral quotient is

    γ J=Π−1,      γ=J(1+Π)/3,      deg γ=2.

Here J²=−3; the degree follows from deg(Π−1)=6. Its cyclic
2-kernel is x=−1: J acts as the identity on B[2], and this
is the entire nontrivial Π-fixed 2-line. Hence γ is the actual
normalized Vélu arrow with that kernel followed by the isomorphism
back to B of differential −1/(1+2ζ). This fixes the coordinate
phase of γ, neither only its quaternion norm nor its sign.
In particular its Vélu target coefficient is 2 and the sixth
power of that differential is 2.

The integer span of 1,ω,γ,ωγ contains 1,ω,Π,ωΠ at index 3:
Π=−1−γ−2ωγ; ωΠ=−ω+2γ+ωγ.
The older block norm in a+bΠ is N(a)+5N(b) for the Eisenstein
norm, yielding absolute polar Gram determinant 15² for the
older four-element basis. The new reduced discriminant is 5,
the algebra discriminant. All four elements are actual integral
endomorphisms; their full span is therefore End(B), because the
index in an integral maximal order would otherwise give an order
discriminant smaller than 5.

The checker constructs the true B[32] basis T,ωT. Use the field
F₂₅(t), t⁸=2+ρ. The defining polynomial is irreducible: t has
t^(5^8)=−t and t^(5^16)=t in the quotient, hence all roots
have exact extension degree 16 over F₅ (a proper subfield
degree divides 8), and the polynomial over F₅ is degree 16.
The polynomial is separable, for its constant is nonzero and
characteristic is 5. Four successive square-root halvings of
(−1,0) are checked by exact group doubling. The two top
basis points are independent since their [16]s are distinct
nonzero 2-torsion points. The checker follows every one of
the 48 primitive cyclic lines through its **actual** five
Vélu arrows and matches the donor's corresponding 16 frames.
It checks γ computed as (Π−1)J⁻¹ on B[32] by direct comparison
to the two true Vélu images. The separate B[3] basis
(0,1),(1,ρ) gives both γ and ω via their actual maps, so it
never divides by 3 at this local sign slot. This lands in the
same B[3] frame for all 16 labels.

## 2. Completely enumerate the signed shell, including Frobenius

Every v in the trace-zero Gross lattice of the bare B is uniquely
v=2u−Tr(u) with u=u₁ω+u₂γ+u₃ωγ. Equivalently, writing J=1+2ω,

    v = (J/3)(t₀+2UΠ),
    U=u₂+u₃ω, t₀=3u₁+2u₂−u₃,
    3 Q(v) = t₀² + 20 (u₂²−u₂u₃+u₃²).

For Q(v)=15q, every |u₂|,|u₃|≤√(3q). For this finite square of
indices the checker solves the t₀ condition exactly by integral
square root and u₁ by divisibility by 3. This is a complete shell,
not a truncated enumeration of small primitive representations.
In each of the 16 literal C₃₂ frames retain only those vectors
where (1+v)/2 acts on that line as the specified root. The odd
fundamental norm implies optimality and (1+v)/2 integral.
At p=5 the exact ramified conductor-one fibre argument of c38823fe,
specialized to level 32 and mod 32 eigenvalue, identifies each
marked vector with one oriented Hilbert class. The marked
automorphisms are ±1: an order-three automorphism has no stable
line on B[2]. No division by 2 or 3 in the multiplicities.
For an independent cardinality check the script enumerates primitive
reduced binary quadratic forms of discriminant Δ, including the
standard boundary convention, and verifies the exact number of
terms for each orientation.

At 3 use the actual nilpotent sign e(v)=Legendre(det(w,vw),3).
All underlying curves share B, and the change of reference mark
can be supported on GL₂(Z₂) alone. Its determinant is a 2-adic
unit. Therefore the fixed χ_{−3} norm gauge is trivial in these
frames; the class sign is e(v)/e(v₀) for one common base v₀.

In B's short formal parameter z=−x/y, Π is z↦z⁵. In the displayed
quaternion expression the A part, with no Π, has no z⁵
term: it commutes with ω, whose short formal parameter acts as
ζ, and with negation, so its only exponents below 7 are degree
one. Since v lies in the maximal division-order ideal at 5,
that linear term is zero. This remains true for denominators
3, which are formal automorphisms. Consequently the actual
c(v) is exactly 2(1+2ζ)(u₂+u₃ζ)/3, not a norm square root
chosen independently of the endomorphism.

On B's dual chart y²=x³+A x+1, Hasse=2A and KS(ω²)=dA/6.
Thus the summand before genus sign is F_s c(v), where
F_s=f₃₂(s)/(12). The Frobenius action verified term-by-term
sends (label,v) to the literal Π label and ΠvΠ⁻¹, followed
only by the correcting power of ω to the donor's frame.
Conjugation by Π in A+BΠ conjugates both Eisenstein coefficients,
while conjugation by ω^j multiplies B by ω^(2j). This computes
the **actual pairs** without reassigning any subset by sign.
The unweighted terms are Frobenius conjugate, the nilpotent signs
are opposite, and every true paired signed sum lies in ρF₅.

Set W=Σ e(v)F_s c(v) across the full class roster. Its
coefficient coordinate for the weight-5/2 coset prescription of
c38823fe is (W−W^5)/(2ρ)=W/ρ. To match the actual based jet multiply
W by e(v₀) and the common scalar 4(−2)ρ/(Δ/5);
−2 is the based primitive quotient's differential factor against
the q-normalized form. For q=1 use the actual first chosen label
of the original control in its odd orientation. In the other
runs use the single explicitly reported base v₀ in the file;
changing that base changes at most the common sign, not zeros
or number of nonzero Frobenius pairs.

## 3. Exact positive and negative outputs in the same ray

In each row choose the smaller C₃₂ root (the opposite orientation
has exactly the same signed raw contraction and number of nonzero
pairs). The based coordinate uses the displayed base in the JSON.

| q | root mod 32 | h(Δ) | nonzero signed Frobenius pairs | W/ρ mod 5 | based jet mod 5 |
|---:|---:|---:|---:|---:|---:|
| 1 | 13 | 2 | 1 | 3 | 4 |
| 17 | 0 | 12 | 5 | 1 | 1 |
| 41 | 3 | 20 | 10 | 4 | 3 |
| 89 | 15 | 28 | 14 | 3 | 1 |
| 193 | 4 | 36 | 13 | 2 | 2 |
| 257 | 13 | 44 | 16 | 0 | 0 |
| 2113 | 4 | 124 | 43 | 0 | 0 |
| 3881 | 3 | 156 | 78 | 0 | 0 |

* q=1 independently recovers the original genuine full CM15 jet 4
  and its two actual marked labels.
* At q=89 the **unsigned** normalized sum is zero in both exact
  orientations, while the genus-weighted whole jet is nonzero.
* q=41 and q=3881 are primes in exactly the same residue class
  modulo 1920=128·3·5. Both have the same ordered C₃₂ roots
  (3,30), same fixed local quadratic types and the same scalar
  Δ/5 modulo 5. Every signed **pair** at both addresses is
  nonzero. Yet all 78 nonzero paired terms at q=3881 cancel in
  the whole signed contraction mod 5. Independently the
  q=193 and q=2113 comparison gives another such positive/zero
  distinction in one exact residue class (latter still has
  43 nonzero paired terms). No ordinary model or chart phase
  changed between the two primes of a pair.

This is a genuine failure of the implication 'a nonzero paired
anchor forces the nonzero whole signed jet', even 'all paired
contributions are nonzero' and after fixing these small local
prime-ray data. It is **not** a proof that the production
ray cannot be controlled by a stronger global theorem, nor that
the q=3881 characteristic-zero trace vanishes. It supplies
neither selected q₂ at N=205042530 nor production rank/point
or additive saturation.

Replay, one standard-library runtime:

    python3 -B donor/check_x032_weighted_hecke.py | cmp - donor/EXACT-X032-HECKE-JET.json
    python3 -B check_actual_whole_cm15_theta.py donor/EXACT-X032-HECKE-JET.json | cmp - EXACT-EIGHT-ACTUAL-THETA-SHELLS.json
    sha256sum -c SHA256SUMS

The finite evaluator uses about 0.45 seconds locally for all
eight complete shell outputs, including torsion charts. It costs
O(q) bounded Eisenstein pair probes per coefficient before
the accepted norms, and fixed precise small level/field tables.
It gives no claim of complexity improvement for huge production
data or of a modest-size full labelled chart at its level.
