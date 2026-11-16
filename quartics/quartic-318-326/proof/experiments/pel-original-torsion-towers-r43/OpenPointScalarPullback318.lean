module
public import AffineOpenEvaluationHolomorphy318
public section
noncomputable section
namespace OpenPointScalarPullback318
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme} (f : Y ⟶ X) (U : X.Opens)

/-- Genuine section evaluation on the actual open subscheme. -/
@[expose] def value (s : Γ(X,U)) (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme) : ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (p.appTop ((LineFrameTopScalar318.ringTop U).inv s))

/-- Exact scalar transport for the ACTUAL inverse-image open and
actual structure-sheaf pullback, before choosing any analytic points. -/
lemma restriction_square (s : Γ(X,U)) :
    (f.resLE U (f ⁻¹ᵁ U) le_rfl).appTop ((LineFrameTopScalar318.ringTop U).inv s)=
      (LineFrameTopScalar318.ringTop (f ⁻¹ᵁ U)).inv (f.app U s) := by
  rw [Scheme.Hom.appTop,Scheme.Hom.resLE_app_top,Scheme.Hom.appLE_eq_app]
  change (LineFrameTopScalar318.ringTop (f ⁻¹ᵁ U)).inv
    (f.app U ((LineFrameTopScalar318.ringTop U).hom
      ((LineFrameTopScalar318.ringTop U).inv s)))=_
  rw [Iso.inv_hom_id_apply]

lemma evaluation_pullback (s : Γ(X,U))
    (q : Spec (CommRingCat.of ℂ) ⟶ (f ⁻¹ᵁ U).toScheme)
    (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (h : q≫(f ⁻¹ᵁ U).ι≫f=p≫U.ι) :
    value U s p=value (f ⁻¹ᵁ U) (f.app U s) q := by
  have he : q≫f.resLE U (f ⁻¹ᵁ U) le_rfl=p := by
    apply (cancel_mono U.ι).1
    rw [Category.assoc,Scheme.Hom.resLE_comp_ι]
    exact h
  rw [←he,value,value]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (q.appTop ((f.resLE U (f ⁻¹ᵁ U) le_rfl).appTop
        ((LineFrameTopScalar318.ringTop U).inv s)))=_
  rw [restriction_square]
end OpenPointScalarPullback318
