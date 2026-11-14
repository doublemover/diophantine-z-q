module
public import PELOriginalOrderPolarizationData318
public section
noncomputable section
namespace PELOriginalOrderPolarizationFrames318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 PELPrincipalOrderCoordinates318
open PELOriginalComplementaryOrder318 PELOriginalComplementaryHermitian318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalOrderPolarizationData318
variable (τ : ℂ) (hτ : 0 < τ.im) (D : Data τ hτ) (a : order)
abbrev power (n : ℕ) := FramedLineTensorPower318.object D.lineData.M n
abbrev powerFrame (n : ℕ) := FramedLineTensorPower318.frames D.lineData.M (O τ hτ) D.lineData.frame n
abbrev firstSheaf := (Scheme.Modules.pullback (act τ hτ a)).obj (power τ hτ D 2)
abbrev secondSheaf := (Scheme.Modules.pullback (act τ hτ (complement a))).obj (power τ hτ D 2)
abbrev productSheaf := IntrinsicTensorSheaf318.tensor (firstSheaf τ hτ D a) (secondSheaf τ hτ D a)
abbrev originalPower := power τ hτ D (2*degree a)
@[expose] def firstFrame (b : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a b).toScheme.ringCatSheaf ≅
      (firstSheaf τ hτ D a).restrict (chart τ hτ a b).ι :=
  OpenLineFrameRefinement318.frame _ _
    (LinePullbackFrames318.frame (act τ hτ a) (power τ hτ D 2) (O τ hτ b.2.1)
      (powerFrame τ hτ D 2 b.2.1)) (chart τ hτ a b) (inf_le_left.trans inf_le_right)
@[expose] def secondFrame (b : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a b).toScheme.ringCatSheaf ≅
      (secondSheaf τ hτ D a).restrict (chart τ hτ a b).ι :=
  OpenLineFrameRefinement318.frame _ _
    (LinePullbackFrames318.frame (act τ hτ (complement a)) (power τ hτ D 2) (O τ hτ b.2.2)
      (powerFrame τ hτ D 2 b.2.2)) (chart τ hτ a b) inf_le_right
@[expose] def productFrame (b : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a b).toScheme.ringCatSheaf ≅
      (productSheaf τ hτ D a).restrict (chart τ hτ a b).ι :=
  TensorLineLocalFrame318.frame _ _ _ (firstFrame τ hτ D a b) (secondFrame τ hτ D a b)
@[expose] def sourceFrame (b : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a b).toScheme.ringCatSheaf ≅
      (originalPower τ hτ D a).restrict (chart τ hτ a b).ι :=
  OpenLineFrameRefinement318.frame _ _ (powerFrame τ hτ D (2*degree a) b.1)
    (chart τ hτ a b) (inf_le_left.trans inf_le_left)
lemma power_transition (n : ℕ) (i j : I τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (O τ hτ i⊓O τ hτ j)) :
    value τ hτ (O τ hτ i⊓O τ hτ j)
      ((LineFrameCocycle318.cocycle (power τ hτ D n) (O τ hτ) (powerFrame τ hτ D n)).transition i j).val z=
        (D.lineData.g j z/D.lineData.g i z)^n := by
  rw [powerFrame,FramedLineTensorPower318.transition,Units.val_pow_eq_pow_val]
  rw [value_eq_evaluation τ hτ _ _ z hz,map_pow,←value_eq_evaluation]
  rw [D.lineData.transition i j z hz.1 hz.2]
lemma pulled_scalar (v : order) (i j : I τ hτ) (W : (candidate τ hτ).Opens)
    (h : W≤act τ hτ v ⁻¹ᵁ (O τ hτ i⊓O τ hτ j)) (z : ComplexVectors)
    (hz : z∈domain τ hτ W) :
    value τ hτ W
      (LineFrameTransitions318.scalar ((Scheme.Modules.pullback (act τ hτ v)).obj (power τ hτ D 2))
        (fun i => act τ hτ v ⁻¹ᵁ O τ hτ i)
        (TranslatedLineIsoScalars318.targetFrame (act τ hτ v) (power τ hτ D 2) (O τ hτ)
          (powerFrame τ hτ D 2)) i j W
        (h.trans ((act τ hτ v).preimage_mono inf_le_left))
        (h.trans ((act τ hτ v).preimage_mono inf_le_right))).val z=
      (D.lineData.g j (linear v z)/D.lineData.g i (linear v z))^2 := by
  rw [TranslatedLineIsoScalars318.target_transition_subopen]
  change value τ hτ W ((candidate τ hτ).presheaf.map (homOfLE h).op
    ((act τ hτ v).app (O τ hτ i⊓O τ hτ j)
      ((LineFrameCocycle318.cocycle (power τ hτ D 2) (O τ hτ)
        (powerFrame τ hτ D 2)).transition i j).val)) z=_
  rw [value_restrict,value_pullback τ hτ (act τ hτ v) (linear v) (act_point τ hτ v)]
  have hm : linear v z∈domain τ hτ (O τ hτ i⊓O τ hτ j) := by
    have hh := h hz
    change act τ hτ v _∈O τ hτ i⊓O τ hτ j at hh
    rw [←Scheme.Hom.comp_apply,act_point] at hh
    exact hh
  exact power_transition τ hτ D 2 i j (linear v z) hm
lemma source_transition (b c : Index τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (chart τ hτ a b⊓chart τ hτ a c)) :
    value τ hτ (chart τ hτ a b⊓chart τ hτ a c)
      ((LineFrameCocycle318.cocycle (originalPower τ hτ D a) (chart τ hτ a)
        (sourceFrame τ hτ D a)).transition b c).val z=
      (D.lineData.g c.1 z/D.lineData.g b.1 z)^(2*degree a) := by
  let W := chart τ hτ a b⊓chart τ hτ a c
  let h : W≤O τ hτ b.1⊓O τ hτ c.1 :=
    le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
      (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have he := LineFrameTransitions318.restrict (originalPower τ hτ D a) (O τ hτ)
    (powerFrame τ hτ D (2*degree a)) b.1 c.1 inf_le_left inf_le_right h
  change value τ hτ W (FrameScalarAlgebra318.scalar _ _).val z=_
  simp only [sourceFrame,OpenLineFrameRefinement318.coordinates]
  rw [←he]
  change value τ hτ W ((candidate τ hτ).presheaf.map (homOfLE h).op
    ((LineFrameCocycle318.cocycle (originalPower τ hτ D a) (O τ hτ)
      (powerFrame τ hτ D (2*degree a))).transition b.1 c.1).val) z=_
  rw [value_restrict,power_transition τ hτ D (2*degree a) b.1 c.1 z (h hz)]
lemma product_transition (b c : Index τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (chart τ hτ a b⊓chart τ hτ a c)) :
    value τ hτ (chart τ hτ a b⊓chart τ hτ a c)
      ((LineFrameCocycle318.cocycle (productSheaf τ hτ D a) (chart τ hτ a)
        (productFrame τ hτ D a)).transition b c).val z=
      (D.lineData.g c.2.1 (linear a z)/D.lineData.g b.2.1 (linear a z))^2*
      (D.lineData.g c.2.2 (linear (complement a) z)/D.lineData.g b.2.2 (linear (complement a) z))^2 := by
  let W := chart τ hτ a b⊓chart τ hτ a c
  have hp : W≤act τ hτ a ⁻¹ᵁ (O τ hτ b.2.1⊓O τ hτ c.2.1) := fun x hx => ⟨hx.1.1.2,hx.2.1.2⟩
  have hm : W≤act τ hτ (complement a) ⁻¹ᵁ (O τ hτ b.2.2⊓O τ hτ c.2.2) := fun x hx => ⟨hx.1.2,hx.2.2⟩
  change value τ hτ W (FrameScalarAlgebra318.scalar _ _).val z=_
  rw [TensorLineCocycle318.scalar_product,Units.val_mul,value_eq_evaluation τ hτ W _ z hz,map_mul]
  rw [←value_eq_evaluation τ hτ W _ z hz,←value_eq_evaluation τ hτ W _ z hz]
  simp only [firstFrame,secondFrame,OpenLineFrameRefinement318.coordinates]
  rw [pulled_scalar τ hτ D a _ _ W hp z hz,pulled_scalar τ hτ D (complement a) _ _ W hm z hz]
end PELOriginalOrderPolarizationFrames318
