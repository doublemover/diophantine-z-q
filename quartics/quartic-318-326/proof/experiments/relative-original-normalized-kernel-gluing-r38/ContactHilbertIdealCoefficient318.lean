module
public import FlatQuotientIdealFlat318
public section
noncomputable section
namespace ContactHilbertIdealCoefficient318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (N : ℕ)
  (D : ContactHilbertData318.BoundedRank S c N)
  (a : (ContactHilbertAvoidanceAffineCover318.cover S c N D).I₀)
local notation "T" => ContactHilbertAvoidanceAffineCover318.ring S c N D a
local notation "A" => ContactHilbertAffineWholeFamily318.sourceRing S c N D a
local notation "f" => ContactHilbertAffineWholeFamily318.affineInto S c N D a
local notation "I" => AffineWholeQuotientProjection318.ideal ℚ A T f
local instance finite : IsFinite (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change IsFinite (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactHilbertAffineWholeFamily318.affine_projection]; infer_instance
local instance flatProjection : Flat (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change Flat (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactHilbertAffineWholeFamily318.affine_projection]; infer_instance
local instance presentation : LocallyOfFinitePresentation (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change LocallyOfFinitePresentation (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactHilbertAffineWholeFamily318.affine_projection]; infer_instance
/-- On the derived WHOLE avoidance coefficient cover, actual standard
bounded Hilbert data have a coefficient-flat full original kernel. -/
lemma kernel_flat : Module.Flat T I := FlatQuotientIdealFlat318.flat T (T ⊗[ℚ] A) I
variable (U : Type) [CommRing U] [Algebra ℚ U] [Algebra T U] [IsScalarTower ℚ T U]
/-- Arbitrary coefficient base change of the ACTUAL recovered original
Hilbert ideal commutes with its module inclusion, not just its quotient. -/
@[expose] def kernelEquiv : U ⊗[T] I ≃ₗ[U] VaryingWholeQuotientTensor318.ideal ℚ A T U I :=
  AffineWholeIdealCoefficient318.equivalence ℚ A T U f
lemma kernelEquiv_unit (i : I) : (kernelEquiv S c N D a U ((1 : U) ⊗ₜ[T] i)).val=
    VaryingWholeQuotientTensor318.source ℚ A T U i.val :=
  AffineWholeIdealCoefficient318.unit_tmul ℚ A T U f i
/-- A genuine regular principal equation, WHEN supplied on this actual
chart, persists over all coefficient rings. Existence of those equations
for every bounded Hilbert point remains the relative Cartier gap. -/
lemma regular_baseChange (d : T ⊗[ℚ] A) (hI : I=Ideal.span ({d} : Set (T ⊗[ℚ] A)))
    (hd : ∀ z : T ⊗[ℚ] A,z*d=0 → z=0) :
    ∀ z : U ⊗[ℚ] A,z*VaryingWholeQuotientTensor318.source ℚ A T U d=0 → z=0 :=
  AffineWholeIdealCoefficient318.principal_regular ℚ A T U f d hI hd
end ContactHilbertIdealCoefficient318
