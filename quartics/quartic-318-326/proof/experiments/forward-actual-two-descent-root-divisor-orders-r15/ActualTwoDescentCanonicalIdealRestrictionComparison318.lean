module
public import ActualTwoDescentCanonicalIdealLocalizationMap318
public import CanonicalRestrictionComparison318
public section
noncomputable section
namespace ActualTwoDescentCanonicalIdealRestrictionComparison318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentIdealLocalizationAdjoint318 ActualTwoDescentCanonicalIdealLocalizationMap318
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R)

def pullbackIso : (Scheme.Modules.pullback (baseMap S)).obj (sourceSheaf I) ≅ targetSheaf S I :=
  (TildePullback318.pullbackIso (CommRingCat.ofHom (algebraMap R S))).app (ModuleCat.of R I) ≪≫
    (tilde.functor (CommRingCat.of S)).mapIso (idealExtensionEquiv S M I).toModuleIso

/-- Exact adjoint identity for the actual canonical localization
comparison,proved through the native composite adjunction. -/
lemma pullback_adjoint :
    (Scheme.Modules.pullbackPushforwardAdjunction (baseMap S)).homEquiv _ _
      (pullbackIso S M I).hom=sheafMap S I := by
  apply ((tilde.adjunction (R:=CommRingCat.of R)).homEquiv _ _).injective
  rw [adjoint_sheafMap]
  apply (cancel_mono (PushforwardGlobalSections318.globalIso
    (CommRingCat.ofHom (algebraMap R S)) (targetSheaf S I)).hom).mp
  have h := TildeComparison318.global_composite (CommRingCat.ofHom (algebraMap R S))
    (ModuleCat.of R I) (ModuleCat.of S (I.map (algebraMap R S)))
      (idealExtensionEquiv S M I).toModuleIso.hom
  simp only [CommRingCat.hom_ofHom] at h
  rw [module_adjoint S M I] at h
  simpa only [pullbackIso,Iso.trans_hom,Functor.mapIso_hom,Iso.app_hom,
    sourceSheaf,targetSheaf,baseMap,tilde.functor,CommRingCat.hom_ofHom,
    moduleToGlobal,Category.assoc,Iso.inv_hom_id,Category.comp_id] using h

variable [IsOpenImmersion (baseMap S)]
def restrictionIso : (sourceSheaf I).restrict (baseMap S) ≅ targetSheaf S I :=
  (TildePullback318.restrictionIso (CommRingCat.ofHom (algebraMap R S))).app (ModuleCat.of R I) ≪≫
    (tilde.functor (CommRingCat.of S)).mapIso (idealExtensionEquiv S M I).toModuleIso

lemma restriction_adjoint : (Scheme.Modules.restrictAdjunction (baseMap S)).homEquiv _ _
    (restrictionIso S M I).hom=sheafMap S I := by
  change (Scheme.Modules.restrictAdjunction _).homEquiv _ _
    ((Scheme.Modules.restrictFunctorIsoPullback _).hom.app _ ≫ (pullbackIso S M I).hom)=_
  rw [CanonicalRestrictionComparison318.restriction_pullback_adjoint,pullback_adjoint]

/-- Whole SHEAF MAP equality. The previous isomorphism is the literal
ideal localization map,not an unspecified unit multiple of it. -/
lemma restrictionIso_hom_eq : (restrictionIso S M I).hom=restrictionMap S I := by
  apply ((Scheme.Modules.restrictAdjunction (baseMap S)).homEquiv _ _).injective
  rw [restriction_adjoint,adjoint_restrictionMap]
end ActualTwoDescentCanonicalIdealRestrictionComparison318
