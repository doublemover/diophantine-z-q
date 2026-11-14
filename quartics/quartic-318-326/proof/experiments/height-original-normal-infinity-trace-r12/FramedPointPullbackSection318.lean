module
public import NormalizedSectionFrame318
public import RestrictionPullbackCoherence318
public section
noncomputable section
namespace FramedPointPullbackSection318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion j]
  (M : Z.Modules) (e : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)

/-- Actual point pullback frame using the genuine open chart, retaining
both the pullback-composition and restriction adjunction comparisons. -/
@[expose] def frame : (Scheme.Modules.pullback (f≫j)).obj M ≅
    SheafOfModules.unit X.ringCatSheaf :=
  ((Scheme.Modules.pullbackComp f j).app M).symm ≪≫
    (Scheme.Modules.pullback f).mapIso ((Scheme.Modules.restrictFunctorIsoPullback j).app M).symm ≪≫
      (Scheme.Modules.pullback f).mapIso e ≪≫ IdentityCotangent318.pullbackUnitIso f

variable (σ : SheafOfModules.unit Z.ringCatSheaf ⟶ M) (a : Γ(Y,⊤))
    (ha : NormalizedSectionFrame318.framedMap j M e σ=ClutchedModule318.multiply a)
include ha in
/-- Entire sheaf-morphism equality for a pulled section, not merely a
claim about coefficients chosen after identifying one-dimensional fibers. -/
theorem section_formula :
    (Scheme.Modules.pullback (f≫j)).map σ≫(frame f j M e).hom=
      (IdentityCotangent318.pullbackUnitIso (f≫j)).hom≫
        ClutchedModule318.multiply (f.appTop a) := by
  have hr : (Scheme.Modules.restrictFunctor j).map σ≫e.hom=
      (Scheme.Modules.restrictUnitIso j).hom≫ClutchedModule318.multiply a := by
    have h := congrArg (fun k => (Scheme.Modules.restrictUnitIso j).hom≫k) ha
    simpa only [NormalizedSectionFrame318.framedMap,←Category.assoc,
      Iso.hom_inv_id,Category.id_comp] using h
  have hn := (Scheme.Modules.restrictFunctorIsoPullback j).inv.naturality σ
  simp only [Functor.comp_map] at hn
  have hi : (Scheme.Modules.pullback j).map σ≫
      (Scheme.Modules.restrictFunctorIsoPullback j).inv.app M≫e.hom=
      (IdentityCotangent318.pullbackUnitIso j).hom≫ClutchedModule318.multiply a := by
    rw [←Category.assoc,hn,Category.assoc,hr]
    rw [←RestrictionPullbackCoherence318.restrict_unit j]
    simp only [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hc := (Scheme.Modules.pullbackComp f j).inv.naturality σ
  simp only [Functor.comp_map] at hc
  calc
    _ = ((Scheme.Modules.pullback (f≫j)).map σ≫
          (Scheme.Modules.pullbackComp f j).inv.app M)≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M≫e.hom)≫
        (IdentityCotangent318.pullbackUnitIso f).hom := by
      simp only [frame,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
        Functor.map_comp,Category.assoc]
    _ = ((Scheme.Modules.pullbackComp f j).inv.app (SheafOfModules.unit Z.ringCatSheaf)≫
          (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback j).map σ))≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M≫e.hom)≫
        (IdentityCotangent318.pullbackUnitIso f).hom := by rw [hc]
    _ = (Scheme.Modules.pullbackComp f j).inv.app (SheafOfModules.unit Z.ringCatSheaf)≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback j).map σ≫
          (Scheme.Modules.restrictFunctorIsoPullback j).inv.app M≫e.hom)≫
        (IdentityCotangent318.pullbackUnitIso f).hom := by
      simp only [Functor.map_comp,Category.assoc]
    _ = (Scheme.Modules.pullbackComp f j).inv.app (SheafOfModules.unit Z.ringCatSheaf)≫
        (Scheme.Modules.pullback f).map (IdentityCotangent318.pullbackUnitIso j).hom≫
        (Scheme.Modules.pullback f).map (ClutchedModule318.multiply a)≫
        (IdentityCotangent318.pullbackUnitIso f).hom := by rw [hi,Functor.map_comp];simp only [Category.assoc]
    _ = _ := by
      rw [PullbackScalar318.pullback_multiply]
      simpa only [Category.assoc] using congrArg
        (fun k => k≫ClutchedModule318.multiply (f.appTop a))
        (PullbackUnitComposition318.inverse_composition f j)

include ha in
lemma normalized_section_formula :
    (IdentityCotangent318.pullbackUnitIso (f≫j)).inv≫
      (Scheme.Modules.pullback (f≫j)).map σ≫(frame f j M e).hom=
        ClutchedModule318.multiply (f.appTop a) := by
  rw [section_formula f j M e σ a ha]
  simp only [←Category.assoc,Iso.inv_hom_id,Category.id_comp]
variable (p : X ⟶ Z) (hp : f≫j=p)
@[expose] def namedFrame : (Scheme.Modules.pullback p).obj M ≅
    SheafOfModules.unit X.ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr hp).app M).symm ≪≫ frame f j M e
include ha in
lemma named_section_formula :
    (IdentityCotangent318.pullbackUnitIso p).inv≫
      (Scheme.Modules.pullback p).map σ≫(namedFrame f j M e p hp).hom=
        ClutchedModule318.multiply (f.appTop a) := by
  subst p
  simpa [namedFrame,Scheme.Modules.pullbackCongr] using
    normalized_section_formula f j M e σ a ha
end FramedPointPullbackSection318
