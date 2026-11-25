# Original R8: coherent degree and adjunction on the same component

**Status:** new Lean files are source-only. No local compiler, cache fetch, repository edit,
publication, or assumption-free model claim. The mathematical identifications below
are separate from the Lean source. The underlying arithmetic scheme, target `π=1728/j`,
retained integral section P, and original field stay fixed.

## 1. Actual component and finite method (not a replacement model)

Use the actual reduced closed integral component i:E↪X from
`OriginalUpperActualFibreComponents318` and the actual codimension-one Cartier
ideal in the regular resolved X. Work over the literal local DVR A at p and its
residue field k. All twists are the restrictions of the specified invertible lines
on X, including the very line from the canonical-differential denominator.

Do not use the restricted original π as a pencil: it is constant on the exceptional
component whose degree matters. Instead construct one **auxiliary** finite flat
h:E→ℙ¹_k on the very same E. An integral proper curve over k is projective
([Stacks 53.2](https://stacks.math.columbia.edu/tag/0BXX)). For an ample power L
choose a nonzero global section s₀ with finite zero scheme T. For large m,
Serre vanishing lifts a generator of Lᵐ|T to s₁ ∈ Γ(E,Lᵐ); a line on the finite
Artinian T is free on its local factors. The pair (s₀ᵐ,s₁) has no common zero.
It is nonconstant since s₀ has some zero (positive degree, or an ample line on
a proper positive-dimension integral scheme cannot have a trivial ample power).
Thus h is proper and quasi-finite, hence finite. Each actual affine ring of
the cover X₀=h⁻¹(𝔸¹_t), X∞=h⁻¹(𝔸¹_s), s=t⁻¹, is finite torsion-free over
the actual coordinate PID, hence finite free. The same holds for the module
of any actual line M on E. No generic pair over an infinite field is used:
this works in the original finite residue field and at 2 and 3.

For kⁿ[T,T⁻¹], write V. In the chosen actual chart bases, the two maps from
the original affine sections are the inclusion of the positive subspace
V₊ and the transport e(V₋) of the negative subspace by the genuine overlap
e∈GLₙ(k[t,t⁻¹]), with negative exponents ≤0. These identifications only
choose bases and change no scheme or support. The true H⁰ is the kernel of the
restriction difference and the true H¹ is its cokernel
([Stacks 30.2](https://stacks.math.columbia.edu/tag/01X8)). All higher
cohomology vanishes. Over k, show the derived boundary respects scalar
multiplication using its naturality for the endomorphism r·id of the actual
sheaf, not the old ℚ-specific additive linearization.

## 2. Two pieces needed for exact relative duality

- `OriginalUpperComponentFiniteHomRestriction318`: inverse to the finite
  affine Hom counit is (m↦[b↦u(bm)]), with literal action ((bℓ)(c)=ℓ(bc)).
  Evaluation at 1 commutes with an actual overlap's base/algebra/module maps.
  In particular the finite-flat pencil can be inseparable; this is not a field
  trace and does not divide by a degree, 2, or 3.
- `OriginalUpperComponentLaurentResidue318`: actual pairing
  ([t^{-1}]\sum_i u_i v_i), monomial test, and finite explicit representative
  of every functional on the true Čech quotient. The original exponent bound
  is obtained from the finitely many columns of e⁻¹, not an added hypothesis.
- `OriginalUpperComponentLaurentDuality318`: this pairs the literal boundary
  annihilator linearly and bijectively with the dual of the genuine quotient.
  This does not yet identify that annihilator with a global sheaf.

The remaining identification is exact, with the following sign:
on the first chart use dt; on the second use ds=−t⁻²dt. Finite Hom
([Stacks 49.5](https://stacks.math.columbia.edu/tag/0FKW)) evaluates at one,
so `h_*(M^∨⊗ω_E)` is `Hom(h_*M,ω_{ℙ¹})` on these very overlaps. If e writes
a column from X∞ in the X₀ basis, the reverse-dual overlap in the dt frame is
(-t^{-2}(e^{-1})^{\mathsf T}). A residue annihilating all tʲ for j≥0
has nonnegative support; one annihilating all tʲ for j≤0 has support ≤−2.
Consequently u in the boundary-annihilator iff u lies in the positive
dual chart and e^T u has support ≤−2, equivalently iff the dual charts
glue, with exact sign. This uses finite Laurent support, not formal
expansions. The explicit next Lean leaf should build that transpose action
from actual column maps and then identify these two support conditions via
`annihilates_supported_iff`. It needs no additional cohomology assumptions.

## 3. Actual weighted degree, and the base normal line

For an effective Cartier divisor D on E and any line M on E, the exact
`0→M→M(D)→M(D)|D→0` gives
`χ_k(M(D))−χ_k(M)=∑_x [κ(x):k]·length(O_{D,x})`.
One can prove the displayed equality directly via the two exact affine
restriction rows and the kernel–cokernel snake lemma; the restriction
difference for the supported sheaf is surjective because finite schemes
have open-and-closed opens. Its local k-masses are exactly the length and
residue factors of the original intersection modules. Replacing an arbitrary
line by the quotient of two effective Cartier lines using high ample powers
then proves tensor additivity without assuming the original stable X comes
with a represented ample line. See also [Stacks 33.44](https://stacks.math.columbia.edu/tag/0AYQ).

Let g:E→Spec k be the original structural map and j:Spec k↪Spec A.
i is Cartier in X, not necessarily in the reducible special fibre. The
actual regular closed immersion and lci transitivity
([Stacks 48.15](https://stacks.math.columbia.edu/tag/0BQV),
[Stacks 109.19](https://stacks.math.columbia.edu/tag/0E6N)) identify
`i^! f^! A = i^*ω_{X/A} ⊗ (I_E/I_E²)^∨` in degree zero:
the source dualizing line has shift +1 and the Cartier i shift −1.
The same composition through the residue base identifies this with
`ω_{E/k} ⊗ g^*(m_A/m_A²)^∨`, since j^!A has shift −1.
Thus the precise line equality on the actual E includes the inverse of the
base normal line. Its degree is zero; use the *given* old prime generator
to trivialize that line if an exact coframe alignment is requested.
This avoids identifying Ω with ω at a node or assuming E smooth. On the
overlap, the chosen Cartier equation's reciprocal transition is precisely
the actual conormal read from `OriginalUpperActualComponentConormal318`.
Neither the regular-immersion duality nor the identification of the already
used global meromorphic ω line with the represented f^!A has been compiled
here. The finite-Laurent method is an alternative to using global Serre
duality as a black box, not an implementation of general f^!.

Duality, once attached, gives `χ_k(ω_E)=-χ_k(O_E)`; hence the needed exact
`deg_k(i^*ω_{X/A}) + deg_k(O_X(E)|E) = -2χ_k(O_E)`.
Keep the constants field k_E=H⁰(E,O_E), since it can strictly contain k.
Both degrees are multiples of f=[k_E:k], by restriction of scalars. In the
exceptional case E²<0, if K·E<0 both are ≤−f; the formula forces both
to equal −f and H¹(E,O_E)=0. The regular-relative Castelnuovo consequence
([Stacks 55.11](https://stacks.math.columbia.edu/tag/0CA6)) is the actual
contradiction to minimality, not an assumption of geometric integrality
over k. This supplies exactly the K·E≥0 row used by the no-ample direct
negative-part argument on the same (X,π) and the same original B.

## 4. Concrete native intake order

1. Earliest independent leaf: `OriginalUpperComponentFiniteHomRestriction318`
   (two official stock roots, no project donor).
2. Unchanged earlier **experimental** sources `LaurentVectorFiltration318` →
   `LaurentTransitionBounds318` → `LaurentCechFinite318` → new residue →
   new duality. `LaurentCechSectionsFinite318` is included only as optional
   subsequent donor. This packet does not claim new or old receipt for these
   particular donor copies; compare their source hashes before accepting.
3. Explicit overlap transition / affine acyclicity / original Cartier and
   relative duality splice, not implemented as a downstream wrapper. The
   repository's `OriginalLineMayerVietorisQuotient318` has an actual
   acyclicity/affine cover route but only an additive quotient. It is not
   bundled or represented as an available compiled dependency here.
