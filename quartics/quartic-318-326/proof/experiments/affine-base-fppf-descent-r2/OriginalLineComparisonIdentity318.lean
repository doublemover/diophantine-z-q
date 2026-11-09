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

/-- The actual identity comparison retains the original line's counit. -/
lemma sheaf_identity :
    (sheafIso (𝟙 R) L).hom ≫ (TildePullbackIdentity318.pullbackId R).hom.app L.object =
      (tilde.functor R).map ((ModuleCat.extendScalarsId R).hom.app
        (OriginalLineAffineModel318.sections R L)) ≫ L.object.fromTildeΓ := by
  let N := OriginalLineAffineModel318.sections R L
  let a := (TildePullback318.pullbackIso (𝟙 R)).app N
  let p := TildePullbackIdentity318.pullbackId R
  rw [sheafIso_counit, Category.assoc, p.hom.naturality]
  change a.inv ≫ p.hom.app ((tilde.functor R).obj N) ≫ L.object.fromTildeΓ = _
  rw [← TildePullbackIdentity318.identity_app R N]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Exact identity for the original affine line global sections. -/
lemma sections_identity :
    (sectionsIso (𝟙 R) L).hom ≫
      moduleSpecΓFunctor.map ((TildePullbackIdentity318.pullbackId R).hom.app L.object) =
        (ModuleCat.extendScalarsId R).hom.app (OriginalLineAffineModel318.sections R L) := by
  have h := congrArg ((tilde.adjunction (R := R)).homEquiv _ _) (sheaf_identity R L)
  simpa only [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    OriginalLineComparisonComposition318.sheafIso_adjoint, canonicalIso_adjoint,
    Category.comp_id] using h
end OriginalLineComparisonIdentity318
