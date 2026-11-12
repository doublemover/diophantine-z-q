module
public import PELOriginalBalancedLineData318
public section
noncomputable section
namespace PELOriginalBalancedLineFrames318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalTranslationFrameValues318 PELOriginalBalancedLineData318
variable (τ : ℂ) (hτ : 0 < τ.im) (D : Data τ hτ) (a : ComplexVectors)
abbrev plus := (Scheme.Modules.pullback (translate τ hτ a)).obj D.M
abbrev minus := (Scheme.Modules.pullback (translate τ hτ (-a))).obj D.M
abbrev balancedSheaf := IntrinsicTensorSheaf318.tensor (plus τ hτ D a) (minus τ hτ D a)
abbrev squareSheaf := FramedLineTensorPower318.object D.M 2
@[expose] def plusFrame (b : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a b).toScheme.ringCatSheaf ≅
      (plus τ hτ D a).restrict (chart τ hτ a b).ι :=
  OpenLineFrameRefinement318.frame _ _
    (LinePullbackFrames318.frame (translate τ hτ a) D.M (O τ hτ b.2.1) (D.frame b.2.1))
    (chart τ hτ a b) (inf_le_left.trans inf_le_right)
@[expose] def minusFrame (b : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a b).toScheme.ringCatSheaf ≅
      (minus τ hτ D a).restrict (chart τ hτ a b).ι :=
  OpenLineFrameRefinement318.frame _ _
    (LinePullbackFrames318.frame (translate τ hτ (-a)) D.M (O τ hτ b.2.2) (D.frame b.2.2))
    (chart τ hτ a b) inf_le_right
@[expose] def balancedFrame (b : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a b).toScheme.ringCatSheaf ≅
      (balancedSheaf τ hτ D a).restrict (chart τ hτ a b).ι :=
  TensorLineLocalFrame318.frame _ _ _ (plusFrame τ hτ D a b) (minusFrame τ hτ D a b)
@[expose] def squareFrame (b : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a b).toScheme.ringCatSheaf ≅
      (squareSheaf τ hτ D).restrict (chart τ hτ a b).ι :=
  OpenLineFrameRefinement318.frame _ _
    (FramedLineTensorPower318.frames D.M (O τ hτ) D.frame 2 b.1)
    (chart τ hτ a b) (inf_le_left.trans inf_le_left)

lemma original_scalar_value (i j : I τ hτ) (W : (candidate τ hτ).Opens)
    (hi : W ≤ O τ hτ i) (hj : W ≤ O τ hτ j) (z : ComplexVectors)
    (hz : z∈domain τ hτ W) :
    value τ hτ W (LineFrameTransitions318.scalar D.M (O τ hτ) D.frame i j W hi hj).val z=
      D.g j z/D.g i z := by
  have h := LineFrameTransitions318.restrict D.M (O τ hτ) D.frame i j
    inf_le_left inf_le_right (le_inf hi hj)
  rw [←h]
  change value τ hτ W ((candidate τ hτ).presheaf.map (homOfLE (le_inf hi hj)).op
    ((LineFrameCocycle318.cocycle D.M (O τ hτ) D.frame).transition i j).val) z=_
  rw [value_restrict]
  exact D.transition i j z (hi hz) (hj hz)

lemma translated_scalar_value (v : ComplexVectors) (i j : I τ hτ)
    (W : (candidate τ hτ).Opens) (h : W ≤ translate τ hτ v ⁻¹ᵁ (O τ hτ i ⊓ O τ hτ j))
    (z : ComplexVectors) (hz : z∈domain τ hτ W) :
    value τ hτ W
      (LineFrameTransitions318.scalar ((Scheme.Modules.pullback (translate τ hτ v)).obj D.M)
        (fun i => translate τ hτ v ⁻¹ᵁ O τ hτ i)
        (TranslatedLineIsoScalars318.targetFrame (translate τ hτ v) D.M (O τ hτ) D.frame)
        i j W (h.trans ((translate τ hτ v).preimage_mono inf_le_left))
          (h.trans ((translate τ hτ v).preimage_mono inf_le_right))).val z=
      D.g j (z+v)/D.g i (z+v) := by
  rw [TranslatedLineIsoScalars318.target_transition_subopen]
  change value τ hτ W ((candidate τ hτ).presheaf.map (homOfLE h).op
    ((translate τ hτ v).app (O τ hτ i ⊓ O τ hτ j)
      ((LineFrameCocycle318.cocycle D.M (O τ hτ) D.frame).transition i j).val)) z=_
  rw [value_restrict,value_pullback τ hτ (translate τ hτ v) (fun w => w+v) (translate_point τ hτ v)]
  have hm : z+v∈domain τ hτ (O τ hτ i ⊓ O τ hτ j) := by
    have hh := h hz
    change translate τ hτ v _∈O τ hτ i ⊓ O τ hτ j at hh
    rw [←Scheme.Hom.comp_apply,translate_point] at hh
    exact hh
  exact D.transition i j (z+v) hm.1 hm.2

lemma square_transition_value (b c : Index τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (chart τ hτ a b ⊓ chart τ hτ a c)) :
    value τ hτ (chart τ hτ a b ⊓ chart τ hτ a c)
      ((LineFrameCocycle318.cocycle (squareSheaf τ hτ D) (chart τ hτ a)
        (squareFrame τ hτ D a)).transition b c).val z=(D.g c.1 z/D.g b.1 z)^2 := by
  let W := chart τ hτ a b ⊓ chart τ hτ a c
  let h : W ≤ O τ hτ b.1 ⊓ O τ hτ c.1 :=
    le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
      (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have he := LineFrameTransitions318.restrict (squareSheaf τ hτ D) (O τ hτ)
    (FramedLineTensorPower318.frames D.M (O τ hτ) D.frame 2) b.1 c.1
    inf_le_left inf_le_right h
  change value τ hτ W (FrameScalarAlgebra318.scalar _ _).val z=_
  simp only [squareFrame,OpenLineFrameRefinement318.coordinates]
  rw [←he]
  change value τ hτ W ((candidate τ hτ).presheaf.map (homOfLE h).op
    ((LineFrameCocycle318.cocycle (squareSheaf τ hτ D) (O τ hτ)
      (FramedLineTensorPower318.frames D.M (O τ hτ) D.frame 2)).transition b.1 c.1).val) z=_
  rw [value_restrict,FramedLineTensorPower318.transition,Units.val_pow_eq_pow_val]
  rw [value_eq_evaluation τ hτ _ _ z (h hz),map_pow,←value_eq_evaluation]
  rw [D.transition b.1 c.1 z (h hz).1 (h hz).2]

lemma balanced_transition_value (b c : Index τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (chart τ hτ a b ⊓ chart τ hτ a c)) :
    value τ hτ (chart τ hτ a b ⊓ chart τ hτ a c)
      ((LineFrameCocycle318.cocycle (balancedSheaf τ hτ D a) (chart τ hτ a)
        (balancedFrame τ hτ D a)).transition b c).val z=
      (D.g c.2.1 (z+a)/D.g b.2.1 (z+a))*(D.g c.2.2 (z-a)/D.g b.2.2 (z-a)) := by
  let W := chart τ hτ a b ⊓ chart τ hτ a c
  have hp : W ≤ translate τ hτ a ⁻¹ᵁ (O τ hτ b.2.1 ⊓ O τ hτ c.2.1) :=
    fun x hx => ⟨hx.1.1.2,hx.2.1.2⟩
  have hm : W ≤ translate τ hτ (-a) ⁻¹ᵁ (O τ hτ b.2.2 ⊓ O τ hτ c.2.2) :=
    fun x hx => ⟨hx.1.2,hx.2.2⟩
  change value τ hτ W (FrameScalarAlgebra318.scalar _ _).val z=_
  rw [TensorLineCocycle318.scalar_product]
  rw [Units.val_mul,value_eq_evaluation τ hτ W _ z hz,map_mul]
  rw [←value_eq_evaluation τ hτ W _ z hz,←value_eq_evaluation τ hτ W _ z hz]
  simp only [plusFrame,minusFrame,OpenLineFrameRefinement318.coordinates]
  rw [translated_scalar_value τ hτ D a _ _ W hp z hz,
    translated_scalar_value τ hτ D (-a) _ _ W hm z hz]
  rfl
end PELOriginalBalancedLineFrames318
