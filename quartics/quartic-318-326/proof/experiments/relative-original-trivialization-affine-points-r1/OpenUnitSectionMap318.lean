module
public import OriginalOpenPullbackSections318
public import ModuleTopExt318
public section
noncomputable section
namespace OpenUnitSectionMap318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (M : X.Modules) (s : Γ(M,⊤))
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal restriction of the original O-linear section map, with the
canonical unit and actual restriction/pullback comparison retained. -/
@[expose] def compared : SheafOfModules.unit Y.ringCatSheaf ⟶ (Scheme.Modules.pullback j).obj M :=
  (Scheme.Modules.restrictUnitIso j).inv ≫
    (Scheme.Modules.restrictFunctor j).map (ModuleGlobalSections318.ofTop M s) ≫
      (Scheme.Modules.restrictFunctorIsoPullback j).hom.app M

lemma compared_eq : compared j M s=ModuleGlobalSections318.ofTop
    ((Scheme.Modules.pullback j).obj M) (OriginalOpenPullbackSections318.sectionPull j M s) := by
  apply ModuleTopExt318.ext
  rw [ModuleTopMorphisms318.ofTop_top_one]
  apply (OriginalOpenPullbackSections318.sectionsEquiv j M).injective
  rw [OriginalOpenPullbackSections318.unit_sections]
  let e := (Scheme.Modules.restrictFunctorIsoPullback j).app M
  have hu : (Scheme.Modules.restrictUnitIso j).inv.app ⊤
      (show Γ(Y,⊤) from 1)=(show Γ(X,j ''ᵁ ⊤) from 1) :=
    map_one (j.appIso ⊤).inv.hom
  change e.inv.app ⊤ (e.hom.app ⊤
    ((ModuleGlobalSections318.ofTop M s).app (j ''ᵁ ⊤)
      ((Scheme.Modules.restrictUnitIso j).inv.app ⊤ (show Γ(Y,⊤) from 1))))=_
  rw [hu]
  have hc (x : Γ(M,j ''ᵁ ⊤)) : e.inv.app ⊤ (e.hom.app ⊤ x)=x :=
    congrArg (fun f => f.app ⊤ x) e.hom_inv_id
  rw [hc]
  exact ModuleGlobalSections318.ofTop_one M s (j ''ᵁ ⊤)

lemma isIso_iff : IsIso ((Scheme.Modules.restrictFunctor j).map
      (ModuleGlobalSections318.ofTop M s)) ↔
    IsIso (ModuleGlobalSections318.ofTop ((Scheme.Modules.pullback j).obj M)
      (OriginalOpenPullbackSections318.sectionPull j M s)) := by
  rw [←compared_eq]
  constructor
  · intro h
    letI := h
    unfold compared
    infer_instance
  · intro h
    letI := h
    have he : (Scheme.Modules.restrictFunctor j).map (ModuleGlobalSections318.ofTop M s)=
        (Scheme.Modules.restrictUnitIso j).hom ≫ compared j M s ≫
          (Scheme.Modules.restrictFunctorIsoPullback j).inv.app M := by
      let e := (Scheme.Modules.restrictFunctorIsoPullback j).app M
      change _=(Scheme.Modules.restrictUnitIso j).hom ≫
        ((Scheme.Modules.restrictUnitIso j).inv ≫
          (Scheme.Modules.restrictFunctor j).map (ModuleGlobalSections318.ofTop M s) ≫ e.hom) ≫ e.inv
      simp only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id,Category.comp_id]
    rw [he]
    infer_instance
end OpenUnitSectionMap318
