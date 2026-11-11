module
public import VaryingPointIdealNaturality318
public section
noncomputable section
namespace VaryingNormalizedGlobalPoint318
open AlgebraicGeometry CategoryTheory
open VaryingSourceFreeQuotientClassifier318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (d : VaryingNormalizedWordParameter318.Point R A ι w S)
local notation "a" => VaryingNormalizedWordFrame318.cyclic R A ι w S d
local notation "hw" => VaryingNormalizedWordFrame318.determinant_unit R A ι w S d
lemma normalized_point : VaryingCyclicNormalizedChart318.point R A ι S a w hw=d := by
  apply VaryingCyclicPointNaturality318.point_eq_of_ideal R A ι w S
  exact VaryingCyclicNormalizedChart318.ideal_point R A ι S a w hw
lemma normalized_coordinate : VaryingCyclicNormalizedChart318.coordinate R A ι S a w hw=
    (VaryingNormalizedWordParameter318.points R A ι w S).symm d := by
  apply (VaryingNormalizedWordParameter318.points R A ι w S).injective
  exact (VaryingCyclicNormalizedChart318.coordinate_point R A ι S a w hw).trans
    ((normalized_point R A ι w S d).trans ((VaryingNormalizedWordParameter318.points R A ι w S).apply_symm_apply d).symm)
/-- The global classifier of a normalized chart point is the ORIGINAL
chart inclusion evaluated at that point, not a new map with the same fiber. -/
lemma classify_cyclic : VaryingCyclicGlobalClassifyingMap318.classify R A ι S a=
    Spec.map (CommRingCat.ofHom ((VaryingNormalizedWordParameter318.points R A ι w S).symm d).toRingHom) ≫
      VaryingWordChartGluing318.into R A ι w := by
  have ht := VaryingCyclicGlobalNaturality318.test_formula R A ι S a w S (AlgHom.id R S) hw
  simp only [AlgHom.id_toRingHom,CommRingCat.ofHom_id,Spec.map_id,Category.id_comp,
    VaryingCyclicCoefficientComposition318.map_id] at ht
  rw [ht,VaryingCyclicNormalizedChart318.schemeMap,normalized_coordinate]
@[expose] def ideal : VaryingFreeIdealClassifyingMap318.IdealData R A ι S :=
  FreeQuotientFramedClassifier318.toIdeal S (S ⊗[R] A) ι (toFramed R A ι S a)
lemma classify_ideal : VaryingFreeIdealClassifyingMap318.classify R A ι S (ideal R A ι w S d)=
    Spec.map (CommRingCat.ofHom ((VaryingNormalizedWordParameter318.points R A ι w S).symm d).toRingHom) ≫
      VaryingWordChartGluing318.into R A ι w :=
  (VaryingFreeIdealClassifyingMap318.classify_representative R A ι S a).trans (classify_cyclic R A ι w S d)
end VaryingNormalizedGlobalPoint318
