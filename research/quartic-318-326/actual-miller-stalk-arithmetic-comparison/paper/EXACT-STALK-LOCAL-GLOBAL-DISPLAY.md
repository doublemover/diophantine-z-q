# The actual same-primitive polarized stalk cups

This packet contains three **source-only** Lean modules. It does not declare
a new cohomology theory, class-field theorem, Cassels–Tate pairing or axiom.

1. `CTMillerExactStalkCoefficient318.exactStalkCoefficient_eq` chooses
   the certified moved divisors on the same geometric curve, with the exact
   ordinary stalk value noncollision guards, and returns their actual four
   residues in the ratio proved in `CTMillerLiteralFourStalks318`. The
   chosen unit equals the original signed Miller coefficient. The positive
   first point and negative second moved divisor are fixed. No smoothness
   or continuity of these auxiliary point choices is required.
2. `CTMillerStalkCupCoefficients318.stalk_raw_eq` applies that equality
   on the literal pair `(ζ(g), g·ψt(h))`; `stalk_defect_eq` applies
   it on `(dσ(g,h), (gh)·ψt(k))`. The field-unit erasure is on the
   same algebraic closure. These are cochain equalities, not just
   equality of products or matching supports.
3. `CTActualStalkInvariantProfile318.stalk_global_same_primitive`
   transports the existing `W.epsilon` without choosing a new primitive.
   `stalk_actual_invariant_total` then realizes the exact same
   `S.cycles` as both corrected families, including ℝ and every literal
   ℚₚ, and derives the same actual finite invariant sum. The Lean statement
   is valid for any supplied additive invariant maps. This flexibility
   does *not* identify those maps with the canonical arithmetic ones.

## Precise arithmetic use and remaining import boundary

Let (m=2^j), (x∈Ш(E_n)[m]), (y∈Ш(E'_n)[m]). Interpret them as
the same literal continuous all-place classes. For fixed `W` and `S`,
all cochain choices in [Poonen–Stoll, §12.2 pp. 27–28 and Proposition 34
p. 30](https://math.mit.edu/~poonen/papers/sha.pdf#page=28) now match:
`W.hx`, `W.hy`, `W.hPhiLabel` and `W.hPsiLabel` fix their labels;
(mσ=τ), (m²σ=0); the already chosen local (Q_v) realizes
(β_v=mQ_v), with (dβ_v=τ_v); the target uses (φQ_v) and (φσ);
(dε=dσ∪τ'). The local corrected cycle is exactly
((σ_v-dQ_v)∪τ'_v-ε_v), in that orientation. Equality of scalar
cochains transfers continuity from the recorded witnesses.

Mathematically the literal rational expressions of (φ,ψ) are morphisms
of the smooth projective curves by extension from the dense affine open.
Their exceptional formulas really are the limits: at the points where
the respective affine denominator is zero the target abscissa has a pole
(the numerator's constant term is a nonzero multiple of (n²)); at the
source origin the abscissa has the usual pole of order two. The only pole
label is the target point at infinity. They preserve the identity and the
native point-level formula gives (ψφ=[2]). In characteristic zero a
nonconstant elliptic-curve homomorphism is separable; the exact geometric
kernel of (φ) has two points. Therefore (deg φ=2) and (ψ), not
(-ψ), is its dual by the dual isogeny identity and surjectivity of (φ).
This is a paper argument from the actual map formulas; the native finite
point homomorphism is not already a scheme-level duality theorem.

The normalized classical source pairing equals the ordinary four-stalk
ratio by the exact relative Picard/seesaw and divisor-value comparison in
`ct-miller-relative-picard-r1/EXACT-PICARD-WEIL-IDENTIFICATION.md`. There
is no independent target sign choice: for target m-torsion (φU,φV),
choose U′ with ψU′=U for the original lift U ∈ E[2m].
Then (2mU'=mφU=0). Classical dual and level compatibility give
(e_{2m}^{E}(U,V)=e_{2m}^{E'}(U',φV)=e_m^{E'}(φU,φV)).
This is exactly the existing descended target coefficient. No new theorem
input asking a caller to supply “the source- and target-cochain equality”
is justified.

For arithmetic calibration, use the canonical invariant
from continuous H² of the absolute p-adic Galois group with algebraic-closure units
to ℚ/ℤ on the *entire* absolute continuous quotient,
normalized on unramified degree (d) by arithmetic Frobenius and
the carry with uniformizer p for i+j ≥ d giving +1/d.
[Milne, Class Field Theory III §§1.7, 1.9, 2.1](https://jmilne.org/math/CourseNotes/CFT.pdf#page=112)
supplies the requisite absolute unramified coverage; the native finite
arithmetic windows and relative invariants merely supply the
normalization on their image. The actual real order-two class is
normalized to (1/2). Applied with these canonical maps, Poonen–Stoll
§12.2 defines the corrected invariant sum; Proposition 34 identifies it
with the Poincaré Cassels–Tate pairing. Hence the resulting mathematical
statement is

    ⟨φ_*x,y⟩_{E′_n} = ⟨x,ψ_*y⟩_{E_n}.

There is **no** ABHN step in this same-ε comparison. To make ε exist
starting from scratch uses the named global field-unit (H^3=0) theorem
(`MilneH3AtQ` interface). If ε changes by a global 2-cocycle instead,
the only additional global scalar is the canonical ABHN sum of its
single actual difference class; native finite support for that class
has already been derived. Changing (Q_v) independently is not a
corollary about ε and needs classical pairing choice-independence.

The strongest downstream conclusion still needs the **separate**
classical divisible-radical theorem (as opposed to inventing an
arbitrary finite perfect pairing), and actual finite reduced
2-primary groups (T,T'). The canonical elliptic polarizations come
from rational ([O]), so the pairings are alternating, not merely
antisymmetric. On the same reduced (φ,ψ), adjointness implies
ker(ψ̄) = (im φ̄)⊥ by separation on T.
Character extension to the finite target then gives the equality

    |ker ψ̄| · |im φ̄| = |T′|.

The annihilator **index is exactly 1**, and the signed reduced dyadic
valuation defect is therefore
    v₂(|ker ψ̄|) − v₂(|ker φ̄|) =
    v₂(|T′|) − v₂(|T|) ∈ 2ℤ.
This uses neither finiteness of total Sha nor of its odd part.
The paper consequence is not a native unconditional theorem or a claim
of actual rational rank. The finite arithmetic-index identities and
the dyadic Kummer corank bridge are separate.

The earliest genuinely unformalized input for the same selected
profile is the absolute p-adic normalization producer and the
relative Picard representability/rigidification, ordinary divisor
calibration, and arithmetic Poonen–Stoll comparison attached to it.
The returned source does not turn any of these facts into a theorem
caller premise named only “calibrated.” No local build, hosted run or
remote write.
