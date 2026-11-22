module
public import ActualGaussianWeberHenselianPointMap318
public import ActualGaussianWeberSelectedGaussianPrime318
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section

namespace ActualGaussianWeberFullTorsionInertia318

open WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318

variable (L : Type*) [Field L] [DecidableEq L]

/-- Both genuine coordinates of all affine M-torsion points,
not just the squared abscissae of the smaller field. -/
@[expose] def torsionCoordinates (M : ℕ) : Set L :=
  {z | ∃ (x y : L), ∃ hx : (curve L).toAffine.Nonsingular x y,
    M • Point.some x y hx=0 ∧ (z=x ∨ z=y)}

end ActualGaussianWeberFullTorsionInertia318

namespace ActualGaussianWeberFullCoordinateField318

open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberFullTorsionInertia318

variable (A : Type*) [Field A] [Algebra Base A] [DecidableEq A]

/-- Literal field of both coordinates of all M-torsion points in the
fixed ambient algebraic extension. -/
@[expose] def fullField (M : ℕ) : IntermediateField Base A :=
  IntermediateField.adjoin Base (torsionCoordinates A M)

end ActualGaussianWeberFullCoordinateField318

namespace ActualGaussianWeberAlgebraicClosureTorsion318

open ActualGaussianWeberSelectedGaussianPrime318

abbrev Ω := AlgebraicClosure Base

/-- Extension of the exact complex embedding used by the selected
Gaussian prime construction, with its sign unchanged. -/
@[expose] def chosenClosureEmbedding : Ω →+* ℂ := by
  letI : Algebra Base ℂ := complexEmbedding.toAlgebra
  exact (IsAlgClosed.lift : Ω →ₐ[Base] ℂ).toRingHom

theorem extends_chosen_complex (z : Base) :
    chosenClosureEmbedding (algebraMap Base Ω z) = complexEmbedding z := by
  unfold chosenClosureEmbedding
  letI : Algebra Base ℂ := complexEmbedding.toAlgebra
  exact (IsAlgClosed.lift : Ω →ₐ[Base] ℂ).commutes z

end ActualGaussianWeberAlgebraicClosureTorsion318

namespace ActualGaussianWeberOriginalFieldFoundation318

open WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberSelectedGaussianPrime318
open ActualGaussianWeberFullTorsionInertia318 ActualGaussianWeberFullCoordinateField318
open ActualGaussianWeberAlgebraicClosureTorsion318

attribute [local instance] Classical.decEq

/-- The actual inherited Gaussian generator maps to the positive
complex quarter-turn in the very same closure embedding. -/
theorem chosen_closure_positive_I :
    chosenClosureEmbedding (algebraMap Base Ω (algebraMap GaussianInt Base gaussianI)) =
      Complex.I :=
  (extends_chosen_complex (algebraMap GaussianInt Base gaussianI)).trans complexEmbedding_i

/-- Both actual coordinates of the given torsion point enter the
unchanged fullField. This does not choose a new point or field. -/
theorem affine_torsion_coordinates_mem_fullField
    (M : ℕ) (x y : Ω) (hxy : (curve Ω).toAffine.Nonsingular x y)
    (hT : M • Point.some x y hxy=0) :
    x∈fullField Ω M ∧ y∈fullField Ω M := by
  have hx : x∈torsionCoordinates Ω M := ⟨x,y,hxy,hT,Or.inl rfl⟩
  have hy : y∈torsionCoordinates Ω M := ⟨x,y,hxy,hT,Or.inr rfl⟩
  exact ⟨IntermediateField.subset_adjoin Base _ hx,IntermediateField.subset_adjoin Base _ hy⟩

end ActualGaussianWeberOriginalFieldFoundation318
