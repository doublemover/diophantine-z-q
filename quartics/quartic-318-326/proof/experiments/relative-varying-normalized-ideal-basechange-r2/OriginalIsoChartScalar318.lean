module
public import OriginalFunctionTransport318
public section
noncomputable section
namespace OriginalIsoChartScalar318
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Z : Scheme.{u}} {A B : CommRingCat.{u}}
  (e : Z ≅ Spec B) (k : Z ⟶ X) [IsOpenImmersion k]
  (q : Z ⟶ Spec A) (b : A ⟶ B) (hb : e.inv ≫ q = Spec.map b)
  (U : X.Opens) (hk : k ''ᵁ ⊤ = U) (hj : (e.inv ≫ k) ''ᵁ ⊤ = U)

include hb in
/-- Replacing a whole open chart by its specified affine isomorphism
preserves the actual ambient regular function, including the original
structural projection. -/
lemma scalar (a : A) :
    X.presheaf.map (eqToHom hk.symm).op
      ((k.appIso ⊤).inv (q.appTop ((Scheme.ΓSpecIso A).inv a))) =
    OriginalFunctionTransport318.chartScalar (e.inv ≫ k) U hj (b a) := by
  have ht : e.inv.appTop (q.appTop ((Scheme.ΓSpecIso A).inv a)) =
      (Scheme.ΓSpecIso B).inv (b a) := by
    have hn := congrArg (fun m => m a) (Scheme.ΓSpecIso_inv_naturality b)
    rw [← CommRingCat.comp_apply,← Scheme.Hom.comp_appTop,hb]
    exact hn.symm
  have hr := OpenChartSections318.restriction_apply e.inv k
    (q.appTop ((Scheme.ΓSpecIso A).inv a))
  have h := congrArg (fun z => X.presheaf.map (eqToHom hj.symm).op z) hr
  rw [ht,← Functor.map_comp_apply] at h
  exact h
end OriginalIsoChartScalar318
