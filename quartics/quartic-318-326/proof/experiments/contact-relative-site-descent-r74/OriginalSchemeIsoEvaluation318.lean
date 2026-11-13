module
public import OriginalTestCoverCartesian318
public section
noncomputable section
namespace OriginalSchemeIsoEvaluation318
open AlgebraicGeometry CategoryTheory
universe u

/-- The exact original global-section maps of a scheme isomorphism form
an isomorphism in the contravariant direction, without changing ring models. -/
@[expose] def appTopIso {X Y : Scheme.{u}} (i : X ≅ Y) : Γ(Y, ⊤) ≅ Γ(X, ⊤) where
  hom := i.hom.appTop
  inv := i.inv.appTop
  hom_inv_id := by rw [← Scheme.Hom.comp_appTop,i.inv_hom_id] <;> rfl
  inv_hom_id := by rw [← Scheme.Hom.comp_appTop,i.hom_inv_id] <;> rfl

/-- An exact full-test presentation over the same base transfers the
original global-section isomorphism to the original family projection. -/
lemma projection_appTop_isIso {X Y S : Scheme.{u}} (i : X ≅ Y)
    (p : X ⟶ S) (q : Y ⟶ S) (h : i.hom ≫ q = p) [IsIso q.appTop] : IsIso p.appTop := by
  let : IsIso i.hom.appTop := inferInstanceAs (IsIso (appTopIso i).hom)
  rw [← h,Scheme.Hom.comp_appTop]
  infer_instance
end OriginalSchemeIsoEvaluation318
