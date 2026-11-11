module
public import EtaleDifferentialSheaf318
public section
noncomputable section
namespace TildeComparison318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {S T : CommRingCat.{u}} (f : S ⟶ T)

/-- The tilde pullback comparison respects every actual module map, in the precise
    composite adjunction rather than only up to an unspecified isomorphism. -/
theorem adjoint_composite (M : ModuleCat S) (N : ModuleCat T)
    (e : (ModuleCat.extendScalars f.hom).obj M ⟶ N) :
    let adj1 := ((tilde.adjunction (R:=S)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight (TildePullback318.globalNatIso f)
    let adj2 := (ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R:=T))
    adj1.homEquiv _ _ ((TildePullback318.pullbackIso f).hom.app M ≫ (tilde.functor T).map e)=
      adj2.homEquiv _ _ ((tilde.functor T).map e) := by
  dsimp only
  rw [Adjunction.homEquiv_naturality_right,TildePullback318.pullbackIso_adjoint]
  rfl

/-- Explicitly unpacked actual global normalization of the pullback comparison. -/
theorem global_composite (M : ModuleCat S) (N : ModuleCat T)
    (e : (ModuleCat.extendScalars f.hom).obj M ⟶ N) :
    (tilde.adjunction (R:=S)).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).homEquiv _ _
        ((TildePullback318.pullbackIso f).hom.app M ≫ (tilde.functor T).map e)) ≫
      (PushforwardGlobalSections318.globalIso f (tilde (R:=T) N)).hom =
    (ModuleCat.extendRestrictScalarsAdj f.hom).homEquiv _ _ e ≫
      (ModuleCat.restrictScalars f.hom).map (tilde.isoTop (R:=T) N).hom := by
  have h:=adjoint_composite f M N e
  dsimp only at h
  rw [Adjunction.homEquiv_ofNatIsoRight_apply,Adjunction.comp_homEquiv,
    Adjunction.comp_homEquiv] at h
  change _ = (ModuleCat.extendRestrictScalarsAdj f.hom).homEquiv _ _
    ((tilde.adjunction (R:=T)).homEquiv _ _ ((tilde.functor T).map e)) at h
  have he : (tilde.adjunction (R:=T)).homEquiv _ _ ((tilde.functor T).map e)=
      e ≫ (tilde.isoTop (R:=T) N).hom := by
    rw [Adjunction.homEquiv_unit]
    exact (tilde.toTildeΓNatIso (R:=T)).hom.naturality e |>.symm
  rw [he,Adjunction.homEquiv_naturality_right] at h
  exact h
end TildeComparison318
