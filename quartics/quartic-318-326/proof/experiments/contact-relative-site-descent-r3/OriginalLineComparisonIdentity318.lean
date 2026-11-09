module
public import OriginalLineComparisonComposition318
public section
noncomputable section
namespace OriginalLineComparisonIdentity318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineAffineBaseChange318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : CommRingCat.{u}) (L : Line (Spec R))

lemma canonicalIso_adjoint :
    (tilde.adjunction (R := R)).homEquiv _ _ L.object.fromTildeΓ =
      𝟙 (OriginalLineAffineModel318.sections R L) := by
  rw [Adjunction.homEquiv_unit]
  exact (tilde.adjunction (R := R)).right_triangle_components L.object

/-- Categorical cancellation is proved before specializing to the original
sheaf categories, keeping their concrete instance terms out of the proof. -/
lemma comparison_cancellation {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : C ⥤ C) (P : D ⥤ D)
    (a : F ⋙ P ≅ G ⋙ F) (p : P ≅ 𝟭 D) (q : G ≅ 𝟭 C)
    (N : C) (M : D) (f : F.obj N ⟶ M)
    (h : a.hom.app N ≫ F.map (q.hom.app N) = p.hom.app (F.obj N)) :
    (a.inv.app N ≫ P.map f) ≫ p.hom.app M = F.map (q.hom.app N) ≫ f := by
  rw [Category.assoc, p.hom.naturality, ← h]
  change (a.app N).inv ≫ (a.app N).hom ≫ F.map (q.hom.app N) ≫ f = _
  exact (a.app N).inv_hom_id_assoc _

/-- The actual identity comparison retains the original line's counit. -/
lemma sheaf_identity :
    (sheafIso (𝟙 R) L).hom ≫ (TildePullbackIdentity318.pullbackId R).hom.app L.object =
      (tilde.functor R).map ((ModuleCat.extendScalarsId R).hom.app
        (OriginalLineAffineModel318.sections R L)) ≫ L.object.fromTildeΓ := by
  rw [sheafIso_counit]
  exact comparison_cancellation (tilde.functor R) _ _
    (TildePullback318.pullbackIso (𝟙 R))
    (TildePullbackIdentity318.pullbackId R) (ModuleCat.extendScalarsId R)
    (OriginalLineAffineModel318.sections R L) L.object L.object.fromTildeΓ
    (TildePullbackIdentity318.identity_app R (OriginalLineAffineModel318.sections R L))

/-- Exact identity for the original affine line global sections. -/
lemma sections_identity :
    (sectionsIso (𝟙 R) L).hom ≫
      moduleSpecΓFunctor.map ((TildePullbackIdentity318.pullbackId R).hom.app L.object) =
        (ModuleCat.extendScalarsId R).hom.app (OriginalLineAffineModel318.sections R L) := by
  have h := congrArg ((tilde.adjunction (R := R)).homEquiv _ _) (sheaf_identity R L)
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right] at h
  simpa only [Functor.id_obj, OriginalLineComparisonComposition318.sheafIso_adjoint, canonicalIso_adjoint,
    Category.comp_id] using h
end OriginalLineComparisonIdentity318
