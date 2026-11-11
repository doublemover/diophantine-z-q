module
public import VaryingCyclicNormalizedChart318
public import Mathlib.AlgebraicGeometry.Cover.Open
public section
noncomputable section
namespace VaryingCyclicDeterminantCover318
open AlgebraicGeometry CategoryTheory
open VaryingSourceFreeQuotientClassifier318 VaryingSourceTensorAction318
open VaryingSourceSurjectiveCoefficient318 CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S)
@[expose] def delta (w : ι → List A) : S :=
  VaryingMatrixWords318.determinant (VaryingSourceActionClassifier318.point R A ι S a.data).val w
abbrev ring (w : ι → List A) := Localization.Away (delta R A ι S a w)
instance baseAlgebra (w : ι → List A) : Algebra R (ring R A ι S a w) :=
  ((algebraMap S (ring R A ι S a w)).comp (algebraMap R S)).toAlgebra
instance baseTower (w : ι → List A) : IsScalarTower R S (ring R A ι S a w) :=
  IsScalarTower.of_algebraMap_eq' rfl
@[expose] def coefficient (w : ι → List A) : S →ₐ[R] ring R A ι S a w :=
  IsScalarTower.toAlgHom R S (ring R A ι S a w)
@[expose] def localized (w : ι → List A) : Cyclic R A ι (ring R A ι S a w) :=
  VaryingCyclicCoefficientSections318.mapCyclic R A ι S a (ring R A ι S a w) (coefficient R A ι S a w)
lemma unit (w : ι → List A) : IsUnit (VaryingMatrixWords318.determinant
    (VaryingSourceActionClassifier318.point R A ι (ring R A ι S a w) (localized R A ι S a w).data).val w) := by
  rw [← determinant_map R A ι S (ring R A ι S a w) (coefficient R A ι S a w) a.data w]
  exact IsLocalization.Away.algebraMap_isUnit (delta R A ι S a w)

/-- The genuine principal determinant cover of the WHOLE coefficient
spectrum, without assuming any one word basis globally. -/
@[expose] def cover : (Spec (CommRingCat.of S)).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) (delta R A ι S a)
    (VaryingSourceGlobalWordCover318.determinants_span_top R A ι S a.data a.cyclic)).openCover
@[expose] def localMap (w : ι → List A) : Spec (CommRingCat.of (ring R A ι S a w)) ⟶
    VaryingWordChartGluing318.scheme R A ι :=
  VaryingCyclicNormalizedChart318.schemeMap R A ι (ring R A ι S a w)
    (localized R A ι S a w) w (unit R A ι S a w)

/-- The normalized point on each determinant open classifies EXACTLY the
extension of the original full cyclic quotient ideal to that localization. -/
lemma local_ideal (w : ι → List A) :
    let d := VaryingCyclicNormalizedChart318.point R A ι (ring R A ι S a w)
      (localized R A ι S a w) w (unit R A ι S a w)
    ideal (VaryingNormalizedWordFrame318.framed R A ι w (ring R A ι S a w) d).action
      (VaryingNormalizedWordFrame318.framed R A ι w (ring R A ι S a w) d).marked=
    Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S (ring R A ι S a w)
      (coefficient R A ι S a w)).toRingHom (ideal (linearAction R A ι S a.data) a.data.marked) :=
  (VaryingCyclicNormalizedChart318.ideal_point R A ι (ring R A ι S a w)
    (localized R A ι S a w) w (unit R A ι S a w)).trans
      (VaryingCyclicIdealBaseChange318.ideal_map R A ι S a (ring R A ι S a w)
        (coefficient R A ι S a w)).symm
end VaryingCyclicDeterminantCover318
