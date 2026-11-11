module
public import VaryingCyclicUniversalChartFamily318
public import VaryingCyclicGlobalClassifyingMap318
public section
noncomputable section
namespace VaryingCyclicFamilyCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingSourceFreeQuotientClassifier318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S)
local notation "L" w => VaryingCyclicDeterminantCover318.ring R A ι S a w
local notation "aL" w => VaryingCyclicDeterminantCover318.localized R A ι S a w
local notation "c" w => VaryingCyclicDeterminantCover318.coefficient R A ι S a w
local notation "𝒰" => VaryingCyclicDeterminantCover318.cover R A ι S a
abbrev chart (w : ι → List A) := VaryingCyclicFamilyBaseChange318.family R A ι (L w) (aL w)
abbrev into (w : ι → List A) : chart R A ι S a w ⟶ VaryingCyclicFamilyBaseChange318.family R A ι S a :=
  VaryingCyclicFamilyBaseChange318.map R A ι S a (L w) (c w)
abbrev projection (w : ι → List A) := VaryingCyclicFamilyBaseChange318.projection R A ι (L w) (aL w)
lemma cartesian (w : ι → List A) : IsPullback (into R A ι S a w) (projection R A ι S a w)
    (VaryingCyclicFamilyBaseChange318.projection R A ι S a) (𝒰.f w) :=
  VaryingCyclicFamilyBaseChange318.cartesian R A ι S a (L w) (c w)
instance into_open (w : ι → List A) : IsOpenImmersion (into R A ι S a w) :=
  MorphismProperty.of_isPullback (cartesian R A ι S a w).flip inferInstance
/-- Genuine whole-source quotient cover, not a list of field fibers. -/
@[expose] def cover : (VaryingCyclicFamilyBaseChange318.family R A ι S a).OpenCover where
  I₀ := ι → List A
  X := chart R A ι S a
  f := into R A ι S a
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun w => inferInstance⟩
    intro x
    obtain ⟨w,y,hy⟩ := (𝒰.pullback₁ (VaryingCyclicFamilyBaseChange318.projection R A ι S a)).exists_eq x
    let h := cartesian R A ι S a w
    refine ⟨w,h.isoPullback.inv y,?_⟩
    have he := congrArg (fun k : pullback (VaryingCyclicFamilyBaseChange318.projection R A ι S a)
      (𝒰.f w) ⟶ VaryingCyclicFamilyBaseChange318.family R A ι S a => k y) h.isoPullback_inv_fst
    exact he.trans hy
abbrev localMap (w : ι → List A) : chart R A ι S a w ⟶ VaryingWordFamilyGluing318.scheme R A ι :=
  VaryingCyclicUniversalChartFamily318.globalMap R A ι (L w) (aL w) w
    (VaryingCyclicDeterminantCover318.unit R A ι S a w)
lemma local_cartesian (w : ι → List A) : IsPullback (localMap R A ι S a w) (projection R A ι S a w)
    (VaryingWordGlobalFamilyProjection318.projection R A ι) (VaryingCyclicDeterminantCover318.localMap R A ι S a w) :=
  VaryingCyclicUniversalChartFamily318.global_cartesian R A ι (L w) (aL w) w
    (VaryingCyclicDeterminantCover318.unit R A ι S a w)
end VaryingCyclicFamilyCover318
