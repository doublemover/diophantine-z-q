module
public import VaryingCyclicChartIntersections318
public section
noncomputable section
namespace VaryingCyclicGlobalClassifyingMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingSourceFreeQuotientClassifier318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S)
local notation "L" w => VaryingCyclicDeterminantCover318.ring R A ι S a w
local notation "𝒰" => VaryingCyclicDeterminantCover318.cover R A ι S a
local notation "m" => VaryingCyclicDeterminantCover318.localMap R A ι S a

lemma overlap_compatible (w v : ι → List A) :
    pullback.fst (𝒰.f w) (𝒰.f v) ≫ m w=pullback.snd (𝒰.f w) (𝒰.f v) ≫ m v := by
  let D := VaryingCyclicChartIntersections318.ring R A ι S a w v
  let c := VaryingCyclicChartIntersections318.localized R A ι S a w v
  let f := VaryingCyclicChartIntersections318.left R A ι S a w v
  let g := VaryingCyclicChartIntersections318.right R A ι S a w v
  have hw := VaryingCyclicChartIntersections318.word_unit R A ι S a w v w
    (VaryingCyclicChartIntersections318.left_unit R A ι S a w v)
  have hv := VaryingCyclicChartIntersections318.word_unit R A ι S a w v v
    (VaryingCyclicChartIntersections318.right_unit R A ι S a w v)
  have hleft : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ m w=
      VaryingCyclicNormalizedChart318.schemeMap R A ι D c w hw := by
    have h := VaryingCyclicPointNaturality318.schemeMap_natural R A ι w (L w)
      (VaryingCyclicDeterminantCover318.localized R A ι S a w)
      (VaryingCyclicDeterminantCover318.unit R A ι S a w) D f
    simpa only [VaryingCyclicChartIntersections318.left_cyclic] using h
  have hright : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ m v=
      VaryingCyclicNormalizedChart318.schemeMap R A ι D c v hv := by
    have h := VaryingCyclicPointNaturality318.schemeMap_natural R A ι v (L v)
      (VaryingCyclicDeterminantCover318.localized R A ι S a v)
      (VaryingCyclicDeterminantCover318.unit R A ι S a v) D g
    simpa only [VaryingCyclicChartIntersections318.right_cyclic] using h
  let h := VaryingCyclicChartIntersections318.cartesian R A ι S a w v
  apply (cancel_epi h.isoPullback.hom).mp
  rw [← Category.assoc,h.isoPullback_hom_fst,← Category.assoc,h.isoPullback_hom_snd]
  exact hleft.trans ((VaryingCyclicWordIndependence318.schemeMap_eq R A ι D c w v hw hv).trans hright.symm)

/-- Genuine global classifying map of every original cyclic free quotient.
It is glued on the WHOLE determinant cover, without a global word basis. -/
@[expose] def classify : Spec (CommRingCat.of S) ⟶ VaryingWordChartGluing318.scheme R A ι :=
  𝒰.glueMorphisms m (overlap_compatible R A ι S a)
@[reassoc] lemma chart_classify (w : ι → List A) : 𝒰.f w ≫ classify R A ι S a=m w :=
  𝒰.ι_glueMorphisms m (overlap_compatible R A ι S a) w
@[reassoc] lemma over_base : classify R A ι S a ≫ VaryingWordParameterStructure318.structureMap R A ι=
    VaryingSourceCoefficientPullback318.base R S := by
  apply Scheme.Cover.hom_ext 𝒰 _ _
  intro w
  rw [← Category.assoc,chart_classify]
  exact (VaryingCyclicNormalizedChart318.over_base R A ι (L w)
    (VaryingCyclicDeterminantCover318.localized R A ι S a w) w
    (VaryingCyclicDeterminantCover318.unit R A ι S a w)).trans
      (VaryingSourceCoefficientPullback318.coefficient_base R S (L w)
        (VaryingCyclicDeterminantCover318.coefficient R A ι S a w)).symm
end VaryingCyclicGlobalClassifyingMap318
