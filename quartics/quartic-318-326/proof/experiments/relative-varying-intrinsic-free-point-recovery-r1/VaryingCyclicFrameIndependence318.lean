module
public import VaryingCyclicGlobalNaturality318
public section
noncomputable section
namespace VaryingCyclicFrameIndependence318
open AlgebraicGeometry CategoryTheory
open CyclicQuotientEvaluation318 VaryingSourceFreeQuotientClassifier318
open VaryingCyclicNormalizedChart318 VaryingCyclicGlobalClassifyingMap318
open scoped TensorProduct
universe u
section FrameMatrices
variable (S B ι : Type u) [CommRing S] [CommRing B] [Algebra S B]
  [Fintype ι] [DecidableEq ι]
variable (d e : FreeQuotientFramedClassifier318.Framed S B ι)
  (hI : ideal d.action d.marked=ideal e.action e.marked) (w : ι → B)
local notation "q" => CyclicQuotientCanonicalFrame318.equiv d.action e.action d.marked e.marked d.cyclic e.cyclic hI
lemma matrix_unit : IsUnit (LinearMap.toMatrix' q.toLinearMap).det := by
  have he : q.symm.toLinearMap.comp q.toLinearMap=LinearMap.id := by
    ext x
    exact q.symm_apply_apply x
  apply Matrix.isUnit_det_of_left_inverse
    (B := LinearMap.toMatrix' q.symm.toLinearMap)
  rw [← LinearMap.toMatrix'_comp,he,LinearMap.toMatrix'_id]
lemma columns_transform : CyclicWordNormalization318.columns S B ι e w=
    LinearMap.toMatrix' q.toLinearMap * CyclicWordNormalization318.columns S B ι d w := by
  ext i j
  calc
    _=q (evaluation d.action d.marked (w j)) i :=
      (congrFun (CyclicQuotientCanonicalFrame318.equiv_evaluation d.action e.action d.marked e.marked
        d.cyclic e.cyclic hI (w j)) i).symm
    _=(LinearMap.toMatrix' q.toLinearMap *ᵥ evaluation d.action d.marked (w j)) i :=
      (congrFun (LinearMap.toMatrix'_mulVec q.toLinearMap (evaluation d.action d.marked (w j))) i).symm
    _=_ := by simp only [Matrix.mulVec_apply_eq_sum,Matrix.mul_apply,CyclicWordNormalization318.columns]
lemma unit_of_ideal (h : IsUnit (CyclicWordNormalization318.columns S B ι d w).det) :
    IsUnit (CyclicWordNormalization318.columns S B ι e w).det := by
  rw [columns_transform S B ι d e hI w,Matrix.det_mul]
  exact (matrix_unit S B ι d e hI).mul h
end FrameMatrices
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a b : Cyclic R A ι S)
local notation "I" c => ideal (toFramed R A ι S c).action (toFramed R A ι S c).marked
variable (hI : I a=I b) (w : ι → List A)
variable (hw : IsUnit (VaryingMatrixWords318.determinant
  (VaryingSourceActionClassifier318.point R A ι S a.data).val w))
lemma word_unit : IsUnit (VaryingMatrixWords318.determinant
    (VaryingSourceActionClassifier318.point R A ι S b.data).val w) := by
  change IsUnit (VaryingMatrixWords318.columns
    (VaryingSourceActionClassifier318.point R A ι S b.data).val w).det
  rw [← frame_columns R A ι S b w]
  exact unit_of_ideal S (S ⊗[R] A) ι (toFramed R A ι S a) (toFramed R A ι S b) hI
    (fun j => (1 : S) ⊗ₜ[R] (w j).prod) (columns_unit R A ι S a w hw)
lemma same_point : point R A ι S a w hw=point R A ι S b w (word_unit R A ι S a b hI w hw) := by
  apply VaryingCyclicPointNaturality318.point_eq_of_ideal R A ι w S
  exact (ideal_point R A ι S a w hw).trans
    (hI.trans (ideal_point R A ι S b w (word_unit R A ι S a b hI w hw)).symm)
lemma same_chart : schemeMap R A ι S a w hw=
    schemeMap R A ι S b w (word_unit R A ι S a b hI w hw) := by
  have hc : coordinate R A ι S a w hw=coordinate R A ι S b w (word_unit R A ι S a b hI w hw) :=
    congrArg (VaryingNormalizedWordParameter318.points R A ι w S).symm (same_point R A ι S a b hI w hw)
  rw [schemeMap,schemeMap,hc]

/-- The global map depends only on the FULL original ideal. Arbitrary
invertible frame changes do not change the represented parameter point. -/
lemma classify_eq : classify R A ι S a=classify R A ι S b := by
  apply Scheme.Cover.hom_ext (VaryingCyclicDeterminantCover318.cover R A ι S a) _ _
  intro v
  let T := VaryingCyclicDeterminantCover318.ring R A ι S a v
  let f := VaryingCyclicDeterminantCover318.coefficient R A ι S a v
  let aT := VaryingCyclicDeterminantCover318.localized R A ι S a v
  let bT := VaryingCyclicCoefficientSections318.mapCyclic R A ι S b T f
  have hT : ideal (toFramed R A ι T aT).action (toFramed R A ι T aT).marked=
      ideal (toFramed R A ι T bT).action (toFramed R A ι T bT).marked :=
    (VaryingCyclicIdealBaseChange318.ideal_map R A ι S a T f).symm.trans
      ((congrArg (Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom) hI).trans
        (VaryingCyclicIdealBaseChange318.ideal_map R A ι S b T f))
  have ha := VaryingCyclicDeterminantCover318.unit R A ι S a v
  have hb := word_unit R A ι T aT bT hT v ha
  have hfb : IsUnit (f (VaryingCyclicDeterminantCover318.delta R A ι S b v)) := by
    change IsUnit (f (VaryingMatrixWords318.determinant
      (VaryingSourceActionClassifier318.point R A ι S b.data).val v))
    rw [VaryingSourceSurjectiveCoefficient318.determinant_map]
    exact hb
  rw [chart_classify]
  exact (same_chart R A ι T aT bT hT v ha).trans
    (VaryingCyclicGlobalNaturality318.test_formula R A ι S b v T f hfb).symm
end VaryingCyclicFrameIndependence318
