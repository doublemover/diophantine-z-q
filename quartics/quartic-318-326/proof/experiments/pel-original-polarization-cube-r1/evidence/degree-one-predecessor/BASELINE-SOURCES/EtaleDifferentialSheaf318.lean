module
public import TildePullback318
public import ScalarExtensionTensor318
public import CanonicalDifferentialSheafMap318
public section
noncomputable section
namespace EtaleDifferentialSheaf318
open CategoryTheory AlgebraicGeometry KaehlerDifferential
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Actual formally étale base change gives a genuine isomorphism of the pulled-back
    affine differential sheaf with the actual target differential sheaf. -/
@[expose] def pullbackIso [Algebra.FormallyEtale S T] :
    (Scheme.Modules.pullback (CanonicalDifferentialSheafMap318.baseMap (S:=S) (T:=T))).obj
      (AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=S)) ≅
      AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=T) :=
  (TildePullback318.pullbackIso (CommRingCat.ofHom (algebraMap S T))).app
      (ModuleCat.of S (KaehlerDifferential R S)) ≪≫
    (tilde.functor (CommRingCat.of T)).mapIso
      (ScalarExtensionTensor318.kaehlerEquiv (R:=R) (S:=S) (T:=T)).toModuleIso

/-- Actual open restriction, not just a coefficient module, is compatible with actual
    formally étale Kähler base change. -/
@[expose] def restrictionIso [Algebra.FormallyEtale S T]
    [IsOpenImmersion (CanonicalDifferentialSheafMap318.baseMap (S:=S) (T:=T))] :
    (Scheme.Modules.restrictFunctor (CanonicalDifferentialSheafMap318.baseMap (S:=S) (T:=T))).obj
      (AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=S)) ≅
      AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=T) :=
  (TildePullback318.restrictionIso (CommRingCat.ofHom (algebraMap S T))).app
      (ModuleCat.of S (KaehlerDifferential R S)) ≪≫
    (tilde.functor (CommRingCat.of T)).mapIso
      (ScalarExtensionTensor318.kaehlerEquiv (R:=R) (S:=S) (T:=T)).toModuleIso

/-- On a genuine principal localization both étaleness and the open immersion are supplied. -/
@[expose] def principalRestrictionIso (s : S) :
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))))).obj
        (AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=S)) ≅
      AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=Localization.Away s) := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ:=Localization.Away s) (Submonoid.powers s)
  exact restrictionIso
end EtaleDifferentialSheaf318
