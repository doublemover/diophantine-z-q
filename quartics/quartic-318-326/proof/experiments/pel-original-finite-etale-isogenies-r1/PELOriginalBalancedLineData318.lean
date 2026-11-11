module
public import PELOriginalOpenFunctionSeparation318
public import PELOriginalTranslationFrameValues318
public import TensorLineCocycle318
public import FramedLineTensorPower318
public import FramedLineUnitGaugeIso318
public section
noncomputable section
namespace PELOriginalBalancedLineData318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalTranslationFrameValues318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev I := NonemptyIndex τ hτ
abbrev O := opens τ hτ

/-- Inputs for balanced-square comparison. The coefficients must be
ACTUAL regular functions on entire original opens. No line isomorphism,
meromorphic extension, or theorem of square is an input. -/
structure Data where
  M : (candidate τ hτ).Modules
  frame : ∀ i : I τ hτ,SheafOfModules.unit (O τ hτ i).toScheme.ringCatSheaf ≅ M.restrict (O τ hτ i).ι
  g : I τ hτ → ComplexVectors → ℂ
  nonzero : ∀ i z,z∈domain τ hτ (O τ hτ i) → g i z≠0
  transition : ∀ i j z,z∈domain τ hτ (O τ hτ i) → z∈domain τ hτ (O τ hτ j) →
    value τ hτ (O τ hτ i ⊓ O τ hτ j)
      ((LineFrameCocycle318.cocycle M (O τ hτ) frame).transition i j).val z=g j z/g i z
  coefficient : ∀ (a : ComplexVectors) (i j k : I τ hτ),Γ(candidate τ hτ,O τ hτ k)
  coefficient_value : ∀ a k i j z,z∈domain τ hτ (O τ hτ k) →
    value τ hτ (O τ hτ k) (coefficient a i j k) z=g i (z+a)*g j (z-a)/g k z^2

variable (D : Data τ hτ) (a : ComplexVectors)
abbrev Index := I τ hτ × I τ hτ × I τ hτ
@[expose] def chart (b : Index τ hτ) : (candidate τ hτ).Opens :=
  O τ hτ b.1 ⊓ (translate τ hτ a ⁻¹ᵁ O τ hτ b.2.1) ⊓
    (translate τ hτ (-a) ⁻¹ᵁ O τ hτ b.2.2)
lemma covers : (⊤ : (candidate τ hτ).Opens) ≤ ⨆ b,chart τ hτ a b := by
  intro x hx
  obtain ⟨k,hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (coversTop τ hτ (show x∈⊤ from trivial))
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (coversTop τ hτ (show translate τ hτ a x∈⊤ from trivial))
  obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (coversTop τ hτ (show translate τ hτ (-a) x∈⊤ from trivial))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(k,i,j),⟨⟨hk,hi⟩,hj⟩⟩
lemma domain_iff (b : Index τ hτ) (z : ComplexVectors) :
    z∈domain τ hτ (chart τ hτ a b) ↔
      z∈domain τ hτ (O τ hτ b.1) ∧
      z+a∈domain τ hτ (O τ hτ b.2.1) ∧ z-a∈domain τ hτ (O τ hτ b.2.2) := by
  change ((_∈O τ hτ b.1 ∧ translate τ hτ a _∈O τ hτ b.2.1) ∧
    translate τ hτ (-a) _∈O τ hτ b.2.2) ↔ _
  rw [←Scheme.Hom.comp_apply,translate_point,←Scheme.Hom.comp_apply,translate_point]
  simp only [sub_eq_add_neg,and_assoc]

@[expose] def regular (b : Index τ hτ) : Γ(candidate τ hτ,chart τ hτ a b) :=
  (candidate τ hτ).presheaf.map (homOfLE
    (show chart τ hτ a b ≤ O τ hτ b.1 from inf_le_left.trans inf_le_left)).op
      (D.coefficient a b.2.1 b.2.2 b.1)
lemma regular_value (b : Index τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (chart τ hτ a b)) :
    value τ hτ (chart τ hτ a b) (regular τ hτ D a b) z=
      D.g b.2.1 (z+a)*D.g b.2.2 (z-a)/D.g b.1 z^2 := by
  rw [regular,value_restrict]
  exact D.coefficient_value a b.1 b.2.1 b.2.2 z ((domain_iff τ hτ a b z).mp hz).1

/-- The selected balanced coefficient is invertible on the WHOLE
shifted chart, including all nonclosed primes. -/
lemma regular_isUnit (b : Index τ hτ) : IsUnit (regular τ hτ D a b) := by
  let U := chart τ hτ a b
  let π := U.ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ
  letI : LocallyOfFiniteType π := by dsimp [π]; infer_instance
  have hu : IsUnit ((LineFrameTopScalar318.ringTop U).inv (regular τ hτ D a b)) := by
    apply ReducedSchemeGlobalFunctionSeparation318.isUnit π
    intro p hp
    obtain ⟨z,hz,he⟩ := PELOriginalOpenFunctionSeparation318.point_representation τ hτ U p hp
    have hv := regular_value τ hτ D a b z hz
    rw [value_at_point τ hτ U _ z p he] at hv
    have hh := (domain_iff τ hτ a b z).mp hz
    have hn : D.g b.2.1 (z+a)*D.g b.2.2 (z-a)/D.g b.1 z^2≠0 :=
      div_ne_zero (mul_ne_zero (D.nonzero _ _ hh.2.1) (D.nonzero _ _ hh.2.2))
        (pow_ne_zero _ (D.nonzero _ _ hh.1))
    have heU : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (p.appTop ((LineFrameTopScalar318.ringTop U).inv (regular τ hτ D a b)))) := by
      rw [hv]; exact isUnit_iff_ne_zero.mpr hn
    simpa only [←ConcreteCategory.comp_apply,Iso.hom_inv_id,ConcreteCategory.id_apply] using
      heU.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
  simpa only [Iso.inv_hom_id_apply] using hu.map (LineFrameTopScalar318.ringTop U).hom
@[expose] def unit (b : Index τ hτ) : Γ(candidate τ hτ,chart τ hτ a b)ˣ :=
  (regular_isUnit τ hτ D a b).unit
lemma unit_value (b : Index τ hτ) : (unit τ hτ D a b).val=regular τ hτ D a b :=
  (regular_isUnit τ hτ D a b).unit_spec
end PELOriginalBalancedLineData318
