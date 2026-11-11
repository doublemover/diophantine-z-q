module
public import VaryingCyclicWordIndependence318
public section
noncomputable section
namespace VaryingCyclicChartIntersections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingSourceFreeQuotientClassifier318 VaryingCyclicCoefficientSections318
open VaryingCyclicDeterminantCover318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S) (w v : ι → List A)
local notation "L" t => VaryingCyclicDeterminantCover318.ring R A ι S a t
local notation "δ" t => delta R A ι S a t
abbrev ring := Localization.Away (algebraMap S (L w) (δ v))
local notation "D" => ring R A ι S a w v
instance coefficientAlgebra : Algebra S D :=
  ((algebraMap (L w) D).comp (algebraMap S (L w))).toAlgebra
instance coefficientTower : IsScalarTower S (L w) D := IsScalarTower.of_algebraMap_eq' rfl
instance baseAlgebra : Algebra R D := ((algebraMap S D).comp (algebraMap R S)).toAlgebra
instance baseTower : IsScalarTower R S D := IsScalarTower.of_algebraMap_eq' rfl
instance leftTower : IsScalarTower R (L w) D :=
  IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
@[expose] def coefficient : S →ₐ[R] D := IsScalarTower.toAlgHom R S D
@[expose] def left : L w →ₐ[R] D := IsScalarTower.toAlgHom R (L w) D
lemma right_unit : IsUnit (coefficient R A ι S a w v (δ v)) :=
  IsLocalization.Away.algebraMap_isUnit (algebraMap S (L w) (δ v))
@[expose] def right : L v →ₐ[R] D :=
  IsLocalization.Away.liftAlgHom (δ v) (right_unit R A ι S a w v)
lemma left_base : (left R A ι S a w v).comp (VaryingCyclicDeterminantCover318.coefficient R A ι S a w)=
    coefficient R A ι S a w v := by ext s; rfl
lemma right_base : (right R A ι S a w v).comp (VaryingCyclicDeterminantCover318.coefficient R A ι S a v)=
    coefficient R A ι S a w v := by
  ext s
  exact IsLocalization.Away.lift_eq (δ v) (right_unit R A ι S a w v) s

/-- The literal double localization is the actual categorical intersection
of the two original determinant opens of Spec S. -/
lemma cartesian : IsPullback (Spec.map (CommRingCat.ofHom (left R A ι S a w v).toRingHom))
    (Spec.map (CommRingCat.ofHom (right R A ι S a w v).toRingHom))
    ((cover R A ι S a).f w) ((cover R A ι S a).f v) :=
  AffineAwayPullback318.pullback (CommRingCat.ofHom (algebraMap S (L w))) (δ v)
@[expose] def localized : Cyclic R A ι D := mapCyclic R A ι S a D (coefficient R A ι S a w v)
lemma left_cyclic : mapCyclic R A ι (L w) (VaryingCyclicDeterminantCover318.localized R A ι S a w)
    D (left R A ι S a w v)=localized R A ι S a w v := by
  change mapCyclic R A ι (L w)
    (mapCyclic R A ι S a (L w) (VaryingCyclicDeterminantCover318.coefficient R A ι S a w))
      D (left R A ι S a w v)=mapCyclic R A ι S a D (coefficient R A ι S a w v)
  rw [VaryingCyclicCoefficientComposition318.map_comp,left_base]
lemma right_cyclic : mapCyclic R A ι (L v) (VaryingCyclicDeterminantCover318.localized R A ι S a v)
    D (right R A ι S a w v)=localized R A ι S a w v := by
  change mapCyclic R A ι (L v)
    (mapCyclic R A ι S a (L v) (VaryingCyclicDeterminantCover318.coefficient R A ι S a v))
      D (right R A ι S a w v)=mapCyclic R A ι S a D (coefficient R A ι S a w v)
  rw [VaryingCyclicCoefficientComposition318.map_comp,right_base]
lemma left_unit : IsUnit (coefficient R A ι S a w v (δ w)) :=
  (IsLocalization.Away.algebraMap_isUnit (δ w)).map (algebraMap (L w) D)
lemma word_unit (t : ι → List A) (ht : IsUnit (coefficient R A ι S a w v (δ t))) :
    IsUnit (VaryingMatrixWords318.determinant
      (VaryingSourceActionClassifier318.point R A ι D (localized R A ι S a w v).data).val t) := by
  rw [← VaryingSourceSurjectiveCoefficient318.determinant_map R A ι S D
    (coefficient R A ι S a w v) a.data t]
  exact ht
end VaryingCyclicChartIntersections318
