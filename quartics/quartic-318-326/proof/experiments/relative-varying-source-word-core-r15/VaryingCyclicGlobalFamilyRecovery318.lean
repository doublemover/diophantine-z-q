module
public import VaryingCyclicGlobalFamilyLift318
public section
noncomputable section
namespace VaryingCyclicGlobalFamilyRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingSourceFreeQuotientClassifier318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S)
local notation "p" => VaryingCyclicFamilyBaseChange318.projection R A ι S a
local notation "m" => VaryingCyclicGlobalFamilyLift318.map R A ι S a
local notation "c" => VaryingCyclicGlobalClassifyingMap318.classify R A ι S a
local notation "π" => VaryingWordGlobalFamilyProjection318.projection R A ι
local notation "𝒰" => VaryingCyclicDeterminantCover318.cover R A ι S a
/-- Actual global universal-family recovery on every coefficient ring.
The proof uses the whole determinant cover and categorical pullbacks;
there is no assumption that one source-word basis works globally. -/
lemma cartesian : IsPullback m p π c := by
  suffices h : IsPullback p m c π from h.flip
  apply Scheme.isPullback_of_openCover _ _ _ _ 𝒰
  intro w
  let h := VaryingCyclicFamilyCover318.cartesian R A ι S a w
  have hl := (VaryingCyclicFamilyCover318.local_cartesian R A ι S a w).flip
  rw [← VaryingCyclicGlobalClassifyingMap318.chart_classify R A ι S a w] at hl
  change IsPullback (pullback.snd p (𝒰.f w)) (pullback.fst p (𝒰.f w) ≫ m) (𝒰.f w ≫ c) π
  apply hl.of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom,Category.comp_id] using h.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,h.isoPullback_hom_fst]
    exact (VaryingCyclicGlobalFamilyLift318.chart_map R A ι S a w).symm
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
@[expose] def comparison : VaryingCyclicFamilyBaseChange318.family R A ι S a ≅ pullback π c :=
  (cartesian R A ι S a).isoPullback
@[reassoc] lemma comparison_family : (comparison R A ι S a).hom ≫ pullback.fst π c=m :=
  (cartesian R A ι S a).isoPullback_hom_fst
@[reassoc] lemma comparison_base : (comparison R A ι S a).hom ≫ pullback.snd π c=p :=
  (cartesian R A ι S a).isoPullback_hom_snd
@[reassoc] lemma comparison_original : (comparison R A ι S a).hom ≫
    (pullback.fst π c ≫ VaryingWordGlobalOriginalMap318.original R A ι)=
    VaryingCyclicFamilyBaseChange318.into R A ι S a ≫ VaryingSourceCoefficientPullback318.original R A S := by
  rw [← Category.assoc,comparison_family,VaryingCyclicGlobalFamilyLift318.map_original]
end VaryingCyclicGlobalFamilyRecovery318
