module
public import VaryingCyclicIdealBaseChange318
public section
noncomputable section
namespace VaryingCyclicNormalizedChart318
open AlgebraicGeometry CategoryTheory
open VaryingSourceFreeQuotientClassifier318 VaryingSourceTensorAction318
open CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S) (w : ι → List A)
local notation "F" => toFramed R A ι S a
local notation "words" => (fun j => (1 : S) ⊗ₜ[R] (w j).prod)
lemma frame_columns : CyclicWordNormalization318.columns S (S ⊗[R] A) ι F words=
    VaryingMatrixWords318.columns (VaryingSourceActionClassifier318.point R A ι S a.data).val w := by
  ext i j
  exact congrFun (word_evaluation R A ι S a.data (w j)) i
variable (h : IsUnit (VaryingMatrixWords318.determinant
  (VaryingSourceActionClassifier318.point R A ι S a.data).val w))
lemma columns_unit : IsUnit (CyclicWordNormalization318.columns S (S ⊗[R] A) ι F words).det := by
  rw [frame_columns]
  exact h
@[expose] def normalizedFrame : CyclicNormalizedIdealClassifier318.NormalizedFrames S (S ⊗[R] A) ι words :=
  ⟨CyclicWordNormalization318.normalize S (S ⊗[R] A) ι F words (columns_unit R A ι S a w h),
    CyclicWordNormalization318.normalize_is_normalized S (S ⊗[R] A) ι F words (columns_unit R A ι S a w h)⟩
@[expose] def point : VaryingNormalizedWordParameter318.Point R A ι w S :=
  (VaryingNormalizedFrameEquiv318.frames R A ι w S).symm (normalizedFrame R A ι S a w h)
lemma framed_point : VaryingNormalizedWordFrame318.framed R A ι w S (point R A ι S a w h)=
    (normalizedFrame R A ι S a w h).val :=
  congrArg Subtype.val ((VaryingNormalizedFrameEquiv318.frames R A ι w S).apply_symm_apply
    (normalizedFrame R A ι S a w h))

/-- Normalizing a genuine cyclic source action preserves its WHOLE ideal. -/
lemma ideal_point :
    ideal (VaryingNormalizedWordFrame318.framed R A ι w S (point R A ι S a w h)).action
      (VaryingNormalizedWordFrame318.framed R A ι w S (point R A ι S a w h)).marked=
    ideal F.action F.marked := by
  rw [framed_point]
  exact congrArg Subtype.val (CyclicWordNormalization318.normalize_ideal
    S (S ⊗[R] A) ι F words (columns_unit R A ι S a w h))
@[expose] def coordinate : VaryingNormalizedWordParameter318.ring R A ι w →ₐ[R] S :=
  (VaryingNormalizedWordParameter318.points R A ι w S).symm (point R A ι S a w h)
lemma coordinate_point : VaryingNormalizedWordParameter318.toPoint R A ι w S
    (coordinate R A ι S a w h)=point R A ι S a w h :=
  (VaryingNormalizedWordParameter318.points R A ι w S).apply_symm_apply _
@[expose] def schemeMap : Spec (CommRingCat.of S) ⟶ VaryingWordChartGluing318.scheme R A ι :=
  Spec.map (CommRingCat.ofHom (coordinate R A ι S a w h).toRingHom) ≫
    VaryingWordChartGluing318.into R A ι w
@[reassoc] lemma over_base : schemeMap R A ι S a w h ≫
    VaryingWordParameterStructure318.structureMap R A ι=VaryingSourceCoefficientPullback318.base R S := by
  rw [schemeMap,Category.assoc,VaryingWordParameterStructure318.into_structureMap]
  exact VaryingSourceCoefficientPullback318.coefficient_base R
    (VaryingNormalizedWordParameter318.ring R A ι w) S (coordinate R A ι S a w h)
end VaryingCyclicNormalizedChart318
