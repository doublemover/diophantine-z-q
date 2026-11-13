module
public import EvaluatedCotangentExt318
public section
noncomputable section
namespace IntegralGenericCotangentSquare318
open scoped TensorProduct
variable (R A E K : Type*) [CommRing R] [CommRing A] [CommRing E] [CommRing K]
  [Algebra R A] [Algebra R E] [Algebra A E] [IsScalarTower R A E]
  [Algebra A R] [Algebra E R] [IsScalarTower A E R]
  [Algebra R K] [Algebra A K] [Algebra E K]
  [IsScalarTower A R K] [IsScalarTower E R K] [IsScalarTower A E K]
  [Algebra.FormallyEtale A E]

/-- Literal scalar extension of integral evaluated etale transport
agrees with transport evaluated directly in K. The equality is checked on
EVERY universal differential, not inferred from one-dimensionality. -/
theorem square :
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
        (IntegralEtaleCotangent318.transport R A E R) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange E R K K (KaehlerDifferential R E) =
    TensorProduct.AlgebraTensorModule.cancelBaseChange A R K K (KaehlerDifferential R A) ≪≫ₗ
      IntegralEtaleCotangent318.transport R A E K := by
  let ca := TensorProduct.AlgebraTensorModule.cancelBaseChange A R K K (KaehlerDifferential R A)
  let ce := TensorProduct.AlgebraTensorModule.cancelBaseChange E R K K (KaehlerDifferential R E)
  let l := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
    (IntegralEtaleCotangent318.transport R A E R)
  have hh : ca.symm ≪≫ₗ l ≪≫ₗ ce = IntegralEtaleCotangent318.transport R A E K := by
    apply EvaluatedCotangentExt318.equiv_ext R A K
    intro a
    simp only [ca,ce,l,LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,
      IntegralEtaleCotangent318.transport_differential,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,one_smul]
  apply LinearEquiv.ext
  intro x
  have hx := congrArg (fun e => e (ca x)) hh
  simpa only [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using hx

variable (C : Type*) [CommRing C] [Algebra R C] [Algebra C E]
  [IsScalarTower R C E] [Algebra C R] [IsScalarTower C E R]
  [Algebra C K] [IsScalarTower C R K] [IsScalarTower C E K]
  [Algebra.FormallyEtale C E]

/-- Integral two-chart comparison commutes with exact tensor
cancellation after scalar extension, including its inverse etale leg. -/
theorem comparison_square :
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
        (IntegralEtaleCotangent318.comparison R A E R C) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange C R K K (KaehlerDifferential R C) =
    TensorProduct.AlgebraTensorModule.cancelBaseChange A R K K (KaehlerDifferential R A) ≪≫ₗ
      IntegralEtaleCotangent318.comparison R A E K C := by
  have ha := square R A E K
  have hc := square R C E K
  rw [IntegralEtaleCotangent318.comparison,
    TensorProduct.AlgebraTensorModule.congr_trans,
    TensorProduct.AlgebraTensorModule.congr_symm]
  apply LinearEquiv.ext
  intro x
  apply (IntegralEtaleCotangent318.transport R C E K).injective
  have hcx := congrArg (fun e => e
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
      (IntegralEtaleCotangent318.transport R C E R)).symm
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
        (IntegralEtaleCotangent318.transport R A E R) x))) hc
  have hax := congrArg (fun e => e x) ha
  simp only [IntegralEtaleCotangent318.comparison,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply] at hcx hax ⊢
  exact hcx.symm.trans hax
end IntegralGenericCotangentSquare318
