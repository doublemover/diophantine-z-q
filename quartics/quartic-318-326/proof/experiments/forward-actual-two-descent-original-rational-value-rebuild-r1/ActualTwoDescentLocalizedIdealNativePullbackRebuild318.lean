module
public import ActualTwoDescentFractionalGeneratorModuleRebuild318
public import ActualTwoDescentIdealLocalizationAdjoint318
public import TildePullback318
public section
noncomputable section
namespace ActualTwoDescentLocalizedIdealNativePullbackRebuild318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (T : Submonoid R) [IsLocalization T S] (I : Ideal R)
local notation "f" => CommRingCat.ofHom (algebraMap R S)

/-- Native pullback of the literal ideal sheaf, normalized by the actual
localization tensor map rather than an abstract line-bundle choice. -/
def iso :
    (Scheme.Modules.pullback (Spec.map f)).obj
      (tilde (R:=CommRingCat.of R) (ModuleCat.of R I)) ≅
    tilde (R:=CommRingCat.of S) (ModuleCat.of S (I.map (algebraMap R S))) :=
  (TildePullback318.pullbackIso f).app (ModuleCat.of R I) ≪≫
    (tilde.functor (CommRingCat.of S)).mapIso
      (ActualTwoDescentIdealLocalizationAdjoint318.idealExtensionEquiv S T I).toModuleIso

lemma hom_formula : (iso S T I).hom=
    (TildePullback318.pullbackIso f).hom.app (ModuleCat.of R I) ≫
    (tilde.functor (CommRingCat.of S)).map
      (ActualTwoDescentIdealLocalizationAdjoint318.idealExtensionEquiv S T I).toModuleIso.hom := rfl

/-- Exact original ideal inclusion on every one-tensor, inherited from
the specified extension map and not merely inferred from bijectivity. -/
lemma one_tensor (x : I) :
    (ActualTwoDescentIdealLocalizationAdjoint318.idealExtensionEquiv S T I
      ((1:S) ⊗ₜ[R,algebraMap R S] x) : S)=algebraMap R S (x:R) := by
  change (ActualTwoDescentLocalizedIdealTensorEquivalence318.localizedIdealTensorEquiv S T I
    ((1:S) ⊗ₜ[R] x) : S)=_
  rw [ActualTwoDescentLocalizedIdealTensorEquivalence318.actual_localized_ideal_tensor_value,one_mul]
end ActualTwoDescentLocalizedIdealNativePullbackRebuild318
