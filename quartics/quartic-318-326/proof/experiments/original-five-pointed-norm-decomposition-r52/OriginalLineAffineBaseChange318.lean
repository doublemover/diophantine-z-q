module
public import TildePullback318
public import OriginalLineAffineModel318
public import LineSheafPullback318
public section
noncomputable section
namespace OriginalLineAffineBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S : CommRingCat.{u}} (f : R ⟶ S) (L : Line (Spec R))

/-- Actual scalar extension of the original affine global-section module. -/
abbrev extendedSections :=
  (ModuleCat.extendScalars f.hom).obj (OriginalLineAffineModel318.sections R L)

/-- The comparison ends in the unchanged actual original line pullback;
its two factors are the canonical affine pullback comparison and the
actual functor image of the original tilde-Gamma counit. -/
@[expose] def sheafIso : tilde (extendedSections f L) ≅
    (LineSheafPullback318.line (Spec.map f) L).object :=
  ((TildePullback318.pullbackIso f).app (OriginalLineAffineModel318.sections R L)).symm ≪≫
    (Scheme.Modules.pullback (Spec.map f)).mapIso (OriginalLineAffineModel318.canonicalIso R L)

/-- Exact affine global-section base change for every original line,
through the canonical tilde unit and the above original sheaf comparison. -/
@[expose] def sectionsIso : extendedSections f L ≅
    OriginalLineAffineModel318.sections S (LineSheafPullback318.line (Spec.map f) L) :=
  tilde.isoTop (extendedSections f L) ≪≫ moduleSpecΓFunctor.mapIso (sheafIso f L)

@[expose] def sectionsEquiv : extendedSections f L ≃ₗ[S]
    OriginalLineAffineModel318.sections S (LineSheafPullback318.line (Spec.map f) L) :=
  (sectionsIso f L).toLinearEquiv

lemma sheafIso_counit : (sheafIso f L).hom =
    (TildePullback318.pullbackIso f).inv.app (OriginalLineAffineModel318.sections R L) ≫
      (Scheme.Modules.pullback (Spec.map f)).map L.object.fromTildeΓ := rfl

lemma sectionsIso_hom : (sectionsIso f L).hom =
    (tilde.isoTop (extendedSections f L)).hom ≫ moduleSpecΓFunctor.map (sheafIso f L).hom := rfl
/-- The comparison preserves the actual original sheaf morphisms. -/
lemma sheafIso_naturality (N : Line (Spec R)) (h : L.object ⟶ N.object) :
    (tilde.functor S).map ((ModuleCat.extendScalars f.hom).map (moduleSpecΓFunctor.map h)) ≫
      (sheafIso f N).hom =
    (sheafIso f L).hom ≫ (Scheme.Modules.pullback (Spec.map f)).map h := by
  let F := Scheme.Modules.pullback (Spec.map f)
  let a := (TildePullback318.pullbackIso f).inv
  change ((ModuleCat.extendScalars f.hom ⋙ tilde.functor S).map (moduleSpecΓFunctor.map h) ≫
      a.app (moduleSpecΓFunctor.obj N.object)) ≫ F.map N.object.fromTildeΓ =
    (a.app (moduleSpecΓFunctor.obj L.object) ≫ F.map L.object.fromTildeΓ) ≫ F.map h
  calc
    _ = (a.app (moduleSpecΓFunctor.obj L.object) ≫
          (tilde.functor R ⋙ F).map (moduleSpecΓFunctor.map h)) ≫ F.map N.object.fromTildeΓ :=
      congrArg (fun k => k ≫ F.map N.object.fromTildeΓ) (a.naturality (moduleSpecΓFunctor.map h))
    _ = a.app (moduleSpecΓFunctor.obj L.object) ≫
          F.map ((tilde.functor R).map (moduleSpecΓFunctor.map h) ≫ N.object.fromTildeΓ) := by
      rw [Functor.map_comp]
      exact Category.assoc _ _ _
    _ = a.app (moduleSpecΓFunctor.obj L.object) ≫ F.map (L.object.fromTildeΓ ≫ h) :=
      congrArg (fun k => a.app (moduleSpecΓFunctor.obj L.object) ≫ F.map k)
        (Scheme.Modules.fromTildeΓNatTrans.naturality h)
    _ = _ := by rw [Functor.map_comp, Category.assoc]
end OriginalLineAffineBaseChange318
