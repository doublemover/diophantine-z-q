module
public import LocalizedReducedFiber318
public import ReducedBaseTensorSections318
public section
noncomputable section
namespace LocalizedBaseTensorSections318
open scoped TensorProduct
variable {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [IsDomain B] [IsDiscreteValuationRing B] [Field K]
  [Algebra B K] [Algebra R K] [IsScalarTower R B K] [IsFractionRing B K]

/-- A reduced whole affine base fiber supplies the reduced local fiber at
any actual localization. The DVR and integral differential frame remain
explicit geometric requirements; all scalar and tensor expressions are unchanged. -/
theorem integral_sections (M : Submonoid A) [IsLocalization M B]
    (e : KaehlerDifferential R B ≃ₗ[B] B)
    (r : R) (hr0 : algebraMap R B r ≠ 0) (hru : ¬IsUnit (algebraMap R B r))
    [IsReduced (A ⧸ Ideal.span ({algebraMap R A r} : Set A))] (t : K) :
    (∃ x0, IntegralCotangentTensor318.map e x0 = VerticalCotangentSections318.q0 (R := R) t) ∧
    (∃ x1, IntegralCotangentTensor318.map e x1 = VerticalCotangentSections318.q1 (R := R) t) := by
  letI : IsReduced (B ⧸ Ideal.span ({algebraMap R B r} : Set B)) :=
    LocalizedReducedFiber318.base_parameter_reduced M r
  exact ReducedBaseTensorSections318.integral_sections e r hr0 hru t

end LocalizedBaseTensorSections318
