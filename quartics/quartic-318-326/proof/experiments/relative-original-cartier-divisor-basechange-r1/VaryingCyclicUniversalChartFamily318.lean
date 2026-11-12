module
public import VaryingCyclicFamilyBaseChange318
public import VaryingCyclicNormalizedChart318
public section
noncomputable section
namespace VaryingCyclicUniversalChartFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingSourceFreeQuotientClassifier318 CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S) (w : ι → List A)
variable (h : IsUnit (VaryingMatrixWords318.determinant
  (VaryingSourceActionClassifier318.point R A ι S a.data).val w))
local notation "N" => VaryingNormalizedWordParameter318.ring R A ι w
local notation "F" => toFramed R A ι S a
local notation "U" => VaryingNormalizedUniversalFamily318.frame R A ι w
local notation "c" => VaryingCyclicNormalizedChart318.coordinate R A ι S a w h
local notation "d" => VaryingCyclicNormalizedChart318.point R A ι S a w h
lemma universal_point : VaryingNormalizedWordNaturality318.mapPoint R A ι w N S c
    (VaryingNormalizedWordOverlap318.universal R A ι w)=d := by
  have hn := VaryingNormalizedWordNaturality318.toPoint_natural R A ι w N S c (AlgHom.id R N)
  simp only [AlgHom.comp_id] at hn
  exact hn.symm.trans (VaryingCyclicNormalizedChart318.coordinate_point R A ι S a w h)
lemma ideal_map : Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A N S c).toRingHom
    (ideal U.action U.marked)=ideal F.action F.marked := by
  have hi := VaryingNormalizedIdealBaseChange318.ideal_map R A ι w N S c
    (VaryingNormalizedWordOverlap318.universal R A ι w)
  rw [universal_point] at hi
  exact hi.trans (VaryingCyclicNormalizedChart318.ideal_point R A ι S a w h)
@[expose] def quotientMap : CommRingCat.of (VaryingNormalizedUniversalFamily318.quotient R A ι w) ⟶
    CommRingCat.of ((S ⊗[R] A) ⧸ ideal F.action F.marked) :=
  AffineQuotientPushout318.arrow
    (CommRingCat.ofHom (VaryingNormalizedIdealBaseChange318.sourceMap R A N S c).toRingHom)
    _ _ (ideal_map R A ι S a w h)
abbrev map : VaryingCyclicFamilyBaseChange318.family R A ι S a ⟶
    VaryingNormalizedUniversalFamily318.family R A ι w := Spec.map (quotientMap R A ι S a w h)
lemma source_cartesian : IsPullback (VaryingCyclicFamilyBaseChange318.into R A ι S a)
    (map R A ι S a w h) (VaryingSourceCoefficientPullback318.sourceChange R A N S c)
    (VaryingNormalizedUniversalFamily318.intoSource R A ι w) :=
  AffineQuotientPushout318.pullback
    (CommRingCat.ofHom (VaryingNormalizedIdealBaseChange318.sourceMap R A N S c).toRingHom)
    _ _ (ideal_map R A ι S a w h)
/-- Pulling back the actual universal word-chart quotient recovers the
whole original cyclic quotient, not just its module rank or closed points. -/
lemma cartesian : IsPullback (map R A ι S a w h)
    (VaryingCyclicFamilyBaseChange318.projection R A ι S a)
    (VaryingNormalizedUniversalFamily318.projection R A ι w)
    (Spec.map (CommRingCat.ofHom c.toRingHom)) := by
  have hs := (source_cartesian R A ι S a w h).flip.paste_vert
    (VaryingSourceCoefficientPullback318.cartesian R A N S c)
  simpa only [VaryingCyclicFamilyBaseChange318.into_projection,
    VaryingQuotientCoefficientPullback318.into_projection] using hs
abbrev globalMap : VaryingCyclicFamilyBaseChange318.family R A ι S a ⟶
    VaryingWordFamilyGluing318.scheme R A ι :=
  map R A ι S a w h ≫ VaryingWordFamilyGluing318.into R A ι w
lemma global_cartesian : IsPullback (globalMap R A ι S a w h)
    (VaryingCyclicFamilyBaseChange318.projection R A ι S a)
    (VaryingWordGlobalFamilyProjection318.projection R A ι)
    (VaryingCyclicNormalizedChart318.schemeMap R A ι S a w h) :=
  (cartesian R A ι S a w h).paste_horiz (VaryingWordGlobalFamilyCartesian318.square R A ι w)
@[reassoc] lemma global_original : globalMap R A ι S a w h ≫
    VaryingWordGlobalOriginalMap318.original R A ι=
    VaryingCyclicFamilyBaseChange318.into R A ι S a ≫
      VaryingSourceCoefficientPullback318.original R A S := by
  rw [globalMap,Category.assoc,VaryingWordGlobalOriginalMap318.into_original]
  change map R A ι S a w h ≫ (VaryingNormalizedUniversalFamily318.intoSource R A ι w ≫
    VaryingSourceCoefficientPullback318.original R A N)=_
  rw [← Category.assoc,← (source_cartesian R A ι S a w h).w,Category.assoc,
    VaryingSourceCoefficientPullback318.source_original]
end VaryingCyclicUniversalChartFamily318
