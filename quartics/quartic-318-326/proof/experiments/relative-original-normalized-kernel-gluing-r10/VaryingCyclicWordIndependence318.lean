module
public import VaryingCyclicCoefficientComposition318
public section
noncomputable section
namespace VaryingCyclicWordIndependence318
open AlgebraicGeometry CategoryTheory
open VaryingSourceFreeQuotientClassifier318 VaryingCyclicNormalizedChart318
open CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S) (w v : ι → List A)
local notation "det" t => VaryingMatrixWords318.determinant
  (VaryingSourceActionClassifier318.point R A ι S a.data).val t
variable (hw : IsUnit (det w)) (hv : IsUnit (det v))
local notation "dw" => point R A ι S a w hw
local notation "dv" => point R A ι S a v hv
local notation "F" => toFramed R A ι S a
local notation "words" t => (fun j => (1 : S) ⊗ₜ[R] (t j).prod)
lemma overlap_unit : IsUnit (VaryingMatrixWords318.determinant dw.val.val v) := by
  have hc : CyclicWordNormalization318.columns S (S ⊗[R] A) ι
      (VaryingNormalizedWordFrame318.framed R A ι w S dw) (words v)=
      VaryingMatrixWords318.columns dw.val.val v :=
    VaryingNormalizedOverlapFrames318.frame_columns R A ι w S v dw
  change IsUnit (VaryingMatrixWords318.columns dw.val.val v).det
  rw [← hc,framed_point]
  exact CyclicWordFrameOverlap318.unit_after_normalize S (S ⊗[R] A) ι F
    (words w) (columns_unit R A ι S a w hw) (words v) (columns_unit R A ι S a v hv)
@[expose] def overlapPoint : VaryingNormalizedWordOverlap318.Point R A ι w S v :=
  ⟨dw,overlap_unit R A ι S a w v hw hv⟩
lemma transition_point :
    (VaryingNormalizedOverlapFrames318.transition R A ι w S v
      (overlapPoint R A ι S a w v hw hv)).val=dv := by
  apply VaryingCyclicPointNaturality318.point_eq_of_ideal R A ι v S
  exact (VaryingWordIdealOverlap318.transition_ideal R A ι w v S
    (overlapPoint R A ι S a w v hw hv)).trans
      ((ideal_point R A ι S a w hw).trans (ideal_point R A ι S a v hv).symm)
@[expose] def overlapCoordinate : VaryingNormalizedWordOverlap318.ring R A ι w v →ₐ[R] S :=
  (VaryingNormalizedWordOverlap318.pointsOnOpen R A ι w S v).symm
    (overlapPoint R A ι S a w v hw hv)
local notation "k" => overlapCoordinate R A ι S a w v hw hv
lemma left_coordinate : k.comp (VaryingNormalizedWordOverlap318.inclusion R A ι w v)=
    coordinate R A ι S a w hw := by
  ext z
  exact VaryingNormalizedWordOverlap318.fromPoint_inclusion R A ι w S v
    (overlapPoint R A ι S a w v hw hv) z
lemma right_coordinate :
    (k.comp (VaryingNormalizedOverlapScheme318.transitionRing R A ι w v)).comp
      (VaryingNormalizedWordOverlap318.inclusion R A ι v w)=coordinate R A ι S a v hv := by
  apply (VaryingNormalizedWordParameter318.points R A ι v S).injective
  have h := VaryingWordOverlapIso318.transitionRing_evaluate R A ι w v S k
  rw [show VaryingNormalizedWordOverlap318.pointsOnOpen R A ι w S v k=
      overlapPoint R A ι S a w v hw hv from
    (VaryingNormalizedWordOverlap318.pointsOnOpen R A ι w S v).apply_symm_apply _] at h
  exact (congrArg Subtype.val h).trans
    ((transition_point R A ι S a w v hw hv).trans (coordinate_point R A ι S a v hv).symm)

/-- Actual maps to the glued parameter are independent of the chosen
invertible word frame, by factorization through the real regular overlap. -/
lemma schemeMap_eq : schemeMap R A ι S a w hw=schemeMap R A ι S a v hv := by
  have hl : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      VaryingNormalizedOverlapScheme318.into R A ι w v=
      Spec.map (CommRingCat.ofHom (coordinate R A ι S a w hw).toRingHom) := by
    rw [VaryingNormalizedOverlapScheme318.into,← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      (k.comp (VaryingNormalizedWordOverlap318.inclusion R A ι w v)).toRingHom)=_
    rw [left_coordinate]
  have hr : (Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      VaryingNormalizedOverlapScheme318.transition R A ι w v) ≫
      VaryingNormalizedOverlapScheme318.into R A ι v w=
      Spec.map (CommRingCat.ofHom (coordinate R A ι S a v hv).toRingHom) := by
    rw [VaryingNormalizedOverlapScheme318.transition,VaryingNormalizedOverlapScheme318.into,
      ← Spec.map_comp,← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((k.comp (VaryingNormalizedOverlapScheme318.transitionRing R A ι w v)).comp
        (VaryingNormalizedWordOverlap318.inclusion R A ι v w)).toRingHom)=_
    rw [right_coordinate]
  change Spec.map (CommRingCat.ofHom (coordinate R A ι S a w hw).toRingHom) ≫
    VaryingWordChartGluing318.into R A ι w=
      Spec.map (CommRingCat.ofHom (coordinate R A ι S a v hv).toRingHom) ≫
        VaryingWordChartGluing318.into R A ι v
  rw [← hl,← hr]
  simpa only [Category.assoc] using congrArg (fun q => Spec.map (CommRingCat.ofHom k.toRingHom) ≫ q)
    (VaryingWordChartGluing318.glue_condition R A ι w v).symm
end VaryingCyclicWordIndependence318
