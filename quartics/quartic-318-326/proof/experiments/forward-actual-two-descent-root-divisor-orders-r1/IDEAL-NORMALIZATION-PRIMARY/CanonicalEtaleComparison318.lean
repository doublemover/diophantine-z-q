module
public import TildeComparison318
public section
noncomputable section
namespace CanonicalEtaleComparison318
open CategoryTheory AlgebraicGeometry KaehlerDifferential
open scoped TensorProduct ChangeOfRings
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyEtale S T]

/-- The actual étale tensor isomorphism has the universal differential map as its adjoint. -/
theorem module_adjoint :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).homEquiv _ _
      (ScalarExtensionTensor318.kaehlerEquiv (R:=R) (S:=S) (T:=T)).toModuleIso.hom =
    CanonicalDifferentialSheafMap318.differentialModuleMap (R:=R) (S:=S) (T:=T) := by
  ext ω
  change ScalarExtensionTensor318.kaehlerEquiv (R:=R) (S:=S) (T:=T)
    ((1:T) ⊗ₜ[S,algebraMap S T] ω) = KaehlerDifferential.map R R S T ω
  rw [ScalarExtensionTensor318.kaehlerEquiv_tmul,one_smul]

/-- The constructed genuine differential-sheaf pullback isomorphism is exactly
    the actual sheaf morphism induced by the universal derivation. -/
theorem pullback_adjoint :
    (Scheme.Modules.pullbackPushforwardAdjunction
      (CanonicalDifferentialSheafMap318.baseMap (S:=S) (T:=T))).homEquiv _ _
        (EtaleDifferentialSheaf318.pullbackIso (R:=R) (S:=S) (T:=T)).hom =
      CanonicalDifferentialSheafMap318.sheafMap (R:=R) (S:=S) (T:=T) := by
  apply ((tilde.adjunction (R:=CommRingCat.of S)).homEquiv _ _).injective
  rw [CanonicalDifferentialSheafMap318.adjoint_sheafMap]
  apply (cancel_mono (PushforwardGlobalSections318.globalIso
    (CommRingCat.ofHom (algebraMap S T))
      (CanonicalDifferentialSheafMap318.targetSheaf (R:=R) (T:=T))).hom).mp
  have h := TildeComparison318.global_composite
    (CommRingCat.ofHom (algebraMap S T)) (ModuleCat.of S (KaehlerDifferential R S))
      (ModuleCat.of T (KaehlerDifferential R T))
        (ScalarExtensionTensor318.kaehlerEquiv (R:=R) (S:=S) (T:=T)).toModuleIso.hom
  simp only [CommRingCat.hom_ofHom] at h
  rw [module_adjoint (R:=R) (S:=S) (T:=T)] at h
  simpa only [EtaleDifferentialSheaf318.pullbackIso,Iso.trans_hom,
    Functor.mapIso_hom,Iso.app_hom,CanonicalDifferentialSheafMap318.targetSheaf,
    CanonicalDifferentialSheafMap318.sourceSheaf,CanonicalDifferentialSheafMap318.baseMap,
    AffineDifferentialSheaf318.differentialSheaf,tilde.functor,CommRingCat.hom_ofHom,
    CanonicalDifferentialSheafMap318.moduleToGlobal,Category.assoc,Iso.inv_hom_id,Category.comp_id] using h

/-- The canonical pullback morphism is an isomorphism, with no supplied isomorphism premise. -/
theorem canonical_pullback_isIso : IsIso
    (((Scheme.Modules.pullbackPushforwardAdjunction
      (CanonicalDifferentialSheafMap318.baseMap (S:=S) (T:=T))).homEquiv _ _).symm
        (CanonicalDifferentialSheafMap318.sheafMap (R:=R) (S:=S) (T:=T))) := by
  rw [←pullback_adjoint,Equiv.symm_apply_apply]
  infer_instance
end CanonicalEtaleComparison318
