module
public import TildePullback318
public section
noncomputable section
namespace NativeTildeLocalizedModule318
open AlgebraicGeometry CategoryTheory
universe u
variable {R S : CommRingCat.{u}} (f : R ⟶ S)
  (M : ModuleCat.{u} R) (V : ModuleCat.{u} S)
  (E : (ModuleCat.extendScalars f.hom).obj M ≅ V)

/-- Native scheme-module pullback, normalized by the EXISTING adjunction
comparison and the specified actual entire-module base-change isomorphism. -/
@[expose] def pullbackIso :
    (Scheme.Modules.pullback (Spec.map f)).obj (tilde M) ≅ tilde V :=
  (TildePullback318.pullbackIso f).app M ≪≫ (tilde.functor S).mapIso E

lemma hom_formula : (pullbackIso f M V E).hom=
    (TildePullback318.pullbackIso f).hom.app M ≫ (tilde.functor S).map E.hom := rfl

/-- The complete composite retains its actual adjunction normalization;
no comparison is chosen solely because the types are isomorphic. -/
lemma adjoint_normalization :
    let a := ((tilde.adjunction (R:=R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight
      (TildePullback318.globalNatIso f)
    let b := (ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R:=S))
    a.homEquiv _ _ (pullbackIso f M V E).hom=
      b.unit.app M ≫
        (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars f.hom).map
          ((tilde.functor S).map E.hom) := by
  dsimp only
  rw [hom_formula,Adjunction.homEquiv_naturality_right,
    TildePullback318.pullbackIso_adjoint]

/-- When the actual map is an open immersion this is its genuine native
restriction. The open-immersion input is explicit, not inferred from ranks. -/
@[expose] def restrictionIso [IsOpenImmersion (Spec.map f)] :
    (Scheme.Modules.restrictFunctor (Spec.map f)).obj (tilde M) ≅ tilde V :=
  (TildePullback318.restrictionIso f).app M ≪≫ (tilde.functor S).mapIso E

lemma restriction_hom [IsOpenImmersion (Spec.map f)] :
    (restrictionIso f M V E).hom=
      (Scheme.Modules.restrictFunctorIsoPullback (Spec.map f)).hom.app (tilde M) ≫
        (pullbackIso f M V E).hom := by
  simp only [restrictionIso,pullbackIso,TildePullback318.restrictionIso,
    Iso.trans_hom,Functor.mapIso_hom,Category.assoc]
end NativeTildeLocalizedModule318
