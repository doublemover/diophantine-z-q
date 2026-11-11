module
public import PELNormalizerPrincipalConjugation318
public section
noncomputable section
namespace PELPositiveNormalizerMobius318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open QuaternionicPositiveDeterminant318 QuaternionicUnitPeriodTransport318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELPeriodDeterminant318 PELPositiveOrderNormalizer318 PELNormalizerPrincipalConjugation318
open PELJointArithmeticLift318 PELPrincipalThreeFreeAction318 PELPrincipalProperAction318
set_option maxHeartbeats 1600000

@[expose] def matrix (g : positiveNormalizer) : RealMatrices := representation (g.val:B)

theorem matrix_positive (g : positiveNormalizer) : 0<(matrix g).det := by
  change 0<(representation (g.val:B)).det
  rw [representation_det]
  exact_mod_cast g.property.2

theorem matrix_mul (g h : positiveNormalizer) : matrix (g*h)=matrix g*matrix h :=
  representation.map_mul (g.val:B) (h.val:B)
theorem matrix_one : matrix (1:positiveNormalizer)=1 := representation.map_one

@[expose] def baseAction (g : positiveNormalizer) (τ : HalfPlane) : HalfPlane :=
  ⟨mobius (matrix g) τ,mobius_positive_det _ (matrix_positive g) τ τ.property⟩

theorem baseAction_one (τ : HalfPlane) : baseAction 1 τ=τ := by
  apply Subtype.ext
  change mobius (matrix 1) τ=(τ:ℂ)
  rw [matrix_one]
  simp [mobius,denominator,Matrix.one_apply]

theorem baseAction_mul (g h : positiveNormalizer) (τ : HalfPlane) :
    baseAction (g*h) τ=baseAction g (baseAction h τ) := by
  apply Subtype.ext
  change mobius (matrix (g*h)) τ=mobius (matrix g) (mobius (matrix h) τ)
  rw [matrix_mul]
  exact (mobius_comp_positive _ _ (matrix_positive g) (matrix_positive h) τ τ.property).symm

theorem matrix_intertwining (g : positiveNormalizer) (u : principalThree) :
    unitMatrix representation order (principalConjugation g u).val*matrix g=
      matrix g*unitMatrix representation order u.val := by
  change representation (((principalConjugation g u).val:order):B)*representation (g.val:B)=
    representation (g.val:B)*representation ((u.val:order):B)
  rw [←map_mul,←map_mul,original_intertwining]

/-- The SAME original principal-three group is conjugated by the actual
normalizer. No claim is made that the normalizer itself is an integral unit. -/
theorem baseAction_equivariant (g : positiveNormalizer) (u : principalThree) (τ : HalfPlane) :
    baseAction g (u • τ)=principalConjugation g u • baseAction g τ := by
  apply Subtype.ext
  change mobius (matrix g) (mobius (unitMatrix representation order u.val) τ)=
    mobius (unitMatrix representation order (principalConjugation g u).val) (mobius (matrix g) τ)
  have hu : 0<(unitMatrix representation order u.val).det := by rw [determinant u]; norm_num
  have hv : 0<(unitMatrix representation order (principalConjugation g u).val).det := by
    rw [determinant (principalConjugation g u)]
    norm_num
  rw [mobius_comp_positive _ _ (matrix_positive g) hu τ τ.property,
    mobius_comp_positive _ _ hv (matrix_positive g) τ τ.property,matrix_intertwining]
end PELPositiveNormalizerMobius318
