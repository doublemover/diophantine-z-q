module
public import FaithfullyFlatTildeFaithful318
public section
noncomputable section
namespace GeometricAffineDescendedMorphism318
open AlgebraicGeometry CategoryTheory LineSheafClass318 GeometricAffineDescentData318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S : CommRingCat.{u}} [Algebra R S] [Module.FaithfullyFlat R S]

abbrev line (D : Datum R S) :=
  OriginalGeometricAffineLine318.line R S D.line D.overlap D.diagonal D.triple
abbrev comparison (D : Datum R S) :=
  OriginalGeometricAffineLine318.pullbackIso R S D.line D.overlap D.diagonal D.triple

/-- The original affine reconstruction comparison uses precisely the
original descended-module isomorphism and the original line's counit. -/
lemma comparison_hom (D : Datum R S) :
    (comparison D).hom =
      (TildePullback318.pullbackIso (AffineCoalgebraLine318.ringMap R S)).hom.app (descended D) ≫
      (tilde.functor S).map (moduleIso D).hom ≫ D.line.object.fromTildeΓ := by
  change (AffineCoalgebraLine318.pullbackIso R S (coalgebra D) D.line (Iso.refl _)).hom = _
  rw [AffineCoalgebraLine318.pullbackIso_hom]
  simp only [AffineCoalgebraLine318.scalarIso, Iso.trans_hom, Iso.refl_hom, Category.comp_id]
  have hp : ((TildePullback318.pullbackIso (AffineCoalgebraLine318.ringMap R S)).app
      (AffineCoalgebraLine318.baseModule R S (coalgebra D))).hom=
      (TildePullback318.pullbackIso (AffineCoalgebraLine318.ringMap R S)).hom.app (descended D) := rfl
  have hm : (AffineCoalgebraModule318.moduleIso (AffineCoalgebraLine318.ringMap R S).hom
      (AffineCoalgebraLine318.faithfullyFlat R S) (coalgebra D)).hom=(moduleIso D).hom := rfl
  exact congrArg₂ (fun a b => a ≫ (tilde.functor S).map b ≫ D.line.object.fromTildeΓ) hp hm

/-- The descended map is an actual sheaf morphism between the reconstructed
original base lines. -/
@[expose] def map {D E : Datum R S} (h : Hom D E) : (line D).object ⟶ (line E).object :=
  (tilde.functor R).map h.baseModuleMap

/-- Its original pullback square commutes with the actual covering sheaf
map and the exact original reconstruction comparisons. -/
lemma map_commutes {D E : Datum R S} (h : Hom D E) :
    (Scheme.Modules.pullback (Spec.map (AffineCoalgebraLine318.ringMap R S))).map (map h) ≫
      (comparison E).hom = (comparison D).hom ≫ h.sheafHom := by
  let a := (TildePullback318.pullbackIso (AffineCoalgebraLine318.ringMap R S)).hom
  rw [comparison_hom, comparison_hom]
  change (tilde.functor R ⋙ Scheme.Modules.pullback
    (Spec.map (AffineCoalgebraLine318.ringMap R S))).map h.baseModuleMap ≫
      a.app (descended E) ≫ (tilde.functor S).map (moduleIso E).hom ≫
        E.line.object.fromTildeΓ = _
  rw [← Category.assoc, ← Category.assoc, a.naturality h.baseModuleMap]
  simp only [Category.assoc]
  change a.app (descended D) ≫
    (tilde.functor S).map ((ModuleCat.extendScalars (algebraMap R S)).map h.baseModuleMap) ≫
      (tilde.functor S).map (moduleIso E).hom ≫ E.line.object.fromTildeΓ = _
  rw [← Functor.map_comp_assoc, h.baseModuleMap_commutes, Functor.map_comp]
  simp only [Category.assoc]
  have hn : (tilde.functor S).map (moduleSpecΓFunctor.map h.sheafHom) ≫
      E.line.object.fromTildeΓ=D.line.object.fromTildeΓ ≫ h.sheafHom :=
    Scheme.Modules.fromTildeΓNatTrans.naturality h.sheafHom
  exact congrArg (fun k : tilde (OriginalLineAffineModel318.sections S D.line) ⟶ E.line.object =>
    a.app (descended D) ≫ (tilde.functor S).map (moduleIso D).hom ≫ k) hn

/-- The actual descended sheaf morphism is unique, not merely unique as
an abstract module map or up to scalar. -/
lemma map_unique {D E : Datum R S} (h : Hom D E)
    (k : (line D).object ⟶ (line E).object)
    (hk : (Scheme.Modules.pullback (Spec.map (AffineCoalgebraLine318.ringMap R S))).map k ≫
      (comparison E).hom = (comparison D).hom ≫ h.sheafHom) : k = map h := by
  apply FaithfullyFlatTildeFaithful318.pullback_map_injective R S
  apply (cancel_mono (comparison E).hom).mp
  exact hk.trans (map_commutes h).symm

lemma exists_unique_map {D E : Datum R S} (h : Hom D E) :
    ∃! k : (line D).object ⟶ (line E).object,
      (Scheme.Modules.pullback (Spec.map (AffineCoalgebraLine318.ringMap R S))).map k ≫
        (comparison E).hom = (comparison D).hom ≫ h.sheafHom :=
  ⟨map h, map_commutes h, fun k hk => map_unique h k hk⟩
end GeometricAffineDescendedMorphism318
