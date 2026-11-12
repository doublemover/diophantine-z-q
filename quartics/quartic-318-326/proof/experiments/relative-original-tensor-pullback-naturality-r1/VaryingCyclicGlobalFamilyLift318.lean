module
public import VaryingCyclicFamilyCover318
public import SchemeMonoLocalLift318
public import VaryingWordGlobalClosedQuotient318
public section
noncomputable section
namespace VaryingCyclicGlobalFamilyLift318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingSourceFreeQuotientClassifier318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S)
local notation "Q" => VaryingCyclicFamilyBaseChange318.family R A ι S a
local notation "p" => VaryingCyclicFamilyBaseChange318.projection R A ι S a
local notation "q" => VaryingCyclicFamilyBaseChange318.into R A ι S a
local notation "c" => VaryingCyclicGlobalClassifyingMap318.classify R A ι S a
local notation "j" => VaryingWordGlobalAmbient318.into R A ι
local notation "𝒱" => VaryingCyclicFamilyCover318.cover R A ι S a
local notation "g" => VaryingCyclicFamilyCover318.localMap R A ι S a
@[expose] def ambientMap : Q ⟶ VaryingWordGlobalAmbient318.ambient R A ι :=
  pullback.lift (p ≫ c) (q ≫ VaryingSourceCoefficientPullback318.original R A S) (by
    rw [Category.assoc,VaryingCyclicGlobalClassifyingMap318.over_base]
    have ht := congrArg (fun k => q ≫ k) (VaryingSourceCoefficientPullback318.tensor_cartesian R A S).w
    simpa only [← Category.assoc,VaryingCyclicFamilyBaseChange318.into_projection] using ht)
@[reassoc] lemma ambient_projection : ambientMap R A ι S a ≫
    VaryingWordGlobalAmbient318.projection R A ι=p ≫ c := pullback.lift_fst _ _ _
@[reassoc] lemma ambient_original : ambientMap R A ι S a ≫ pullback.snd _ _=
    q ≫ VaryingSourceCoefficientPullback318.original R A S := pullback.lift_snd _ _ _
lemma local_factor (w : ι → List A) : g w ≫ j=𝒱.f w ≫ ambientMap R A ι S a := by
  apply pullback.hom_ext
  · simp only [Category.assoc,VaryingWordGlobalAmbient318.into_projection,ambient_projection]
    rw [(VaryingCyclicFamilyCover318.local_cartesian R A ι S a w).w,
      ← Category.assoc,(VaryingCyclicFamilyCover318.cartesian R A ι S a w).w,
      Category.assoc,VaryingCyclicGlobalClassifyingMap318.chart_classify]
  · simp only [Category.assoc,VaryingWordGlobalAmbient318.into_original,ambient_original]
    rw [VaryingCyclicUniversalChartFamily318.global_original]
    have hs := (VaryingCyclicFamilyBaseChange318.source_cartesian R A ι S a
      (VaryingCyclicDeterminantCover318.ring R A ι S a w)
      (VaryingCyclicDeterminantCover318.coefficient R A ι S a w)).w
    rw [← Category.assoc,← hs,Category.assoc,VaryingSourceCoefficientPullback318.source_original]
/-- The original full quotient family maps to the actual global universal
family; agreement is forced by its closed embedding in the source ambient. -/
@[expose] def map : Q ⟶ VaryingWordFamilyGluing318.scheme R A ι :=
  SchemeMonoLocalLift318.lift 𝒱 j (ambientMap R A ι S a) g (local_factor R A ι S a)
@[reassoc] lemma chart_map (w : ι → List A) : 𝒱.f w ≫ map R A ι S a=g w :=
  SchemeMonoLocalLift318.into_lift 𝒱 j (ambientMap R A ι S a) g (local_factor R A ι S a) w
@[reassoc] lemma map_into : map R A ι S a ≫ j=ambientMap R A ι S a :=
  SchemeMonoLocalLift318.lift_factor 𝒱 j (ambientMap R A ι S a) g (local_factor R A ι S a)
@[reassoc] lemma map_projection : map R A ι S a ≫ VaryingWordGlobalFamilyProjection318.projection R A ι=p ≫ c := by
  rw [← VaryingWordGlobalAmbient318.into_projection,← Category.assoc,map_into,ambient_projection]
@[reassoc] lemma map_original : map R A ι S a ≫ VaryingWordGlobalOriginalMap318.original R A ι=
    q ≫ VaryingSourceCoefficientPullback318.original R A S := by
  rw [← VaryingWordGlobalAmbient318.into_original,← Category.assoc,map_into,ambient_original]
end VaryingCyclicGlobalFamilyLift318
