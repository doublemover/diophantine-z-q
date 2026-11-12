module
public import IntegralEtaleCotangent318
public section
namespace LinearEquivComparisonDiamond318
variable {K : Type*} [CommRing K]
  {A B C E F G : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
  [Module K A] [Module K B] [Module K C]
  [Module K E] [Module K F] [Module K G]

/-- Cancel the SAME refinement maps from a commuting cotangent
diamond. This lemma supplies no geometric commutativity hypotheses. -/
theorem comparison (ae : A ≃ₗ[K] E) (ce : C ≃ₗ[K] E)
    (af : A ≃ₗ[K] F) (bf : B ≃ₗ[K] F) (cb : C ≃ₗ[K] B)
    (eg : E ≃ₗ[K] G) (fg : F ≃ₗ[K] G)
    (ha : ae ≪≫ₗ eg = af ≪≫ₗ fg)
    (hc : ce ≪≫ₗ eg = cb ≪≫ₗ bf ≪≫ₗ fg) :
    ae ≪≫ₗ ce.symm ≪≫ₗ cb = af ≪≫ₗ bf.symm := by
  apply LinearEquiv.ext
  intro x
  apply (bf ≪≫ₗ fg).injective
  have hcx := congrArg (fun e => e (ce.symm (ae x))) hc
  have hax := congrArg (fun e => e x) ha
  simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply] at hcx hax ⊢
  exact hcx.symm.trans hax
end LinearEquivComparisonDiamond318
