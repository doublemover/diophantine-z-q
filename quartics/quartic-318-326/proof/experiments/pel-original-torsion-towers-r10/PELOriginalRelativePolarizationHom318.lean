module
public import PELOriginalCubeTestClasses318
public section
noncomputable section
namespace PELOriginalRelativePolarizationHom318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318 PELOriginalProductChartCover318
open PELOriginalSchemePointGroup318 PELOriginalCubeTestClasses318
open RelativeLineClassQuotient318 RelativeLineClassBaseChange318
variable (τ : ℂ) (hτ : 0 < τ.im) {T : Scheme} (ρ : T ⟶ Spec (CommRingCat.of ℂ))
abbrev Total := pullback (π τ hτ) ρ
abbrev totalBase : Total τ hτ ρ ⟶ Spec (CommRingCat.of ℂ) := pullback.fst (π τ hτ) ρ≫π τ hτ
abbrev parameterMap : Total τ hτ ρ ⟶ T := pullback.snd (π τ hτ) ρ
@[expose] def original : Points τ hτ (Total τ hτ ρ) (totalBase τ hτ ρ) := ⟨pullback.fst _ _,rfl⟩
@[expose] def parameter : Points τ hτ T ρ →+ Points τ hτ (Total τ hτ ρ) (totalBase τ hτ ρ) :=
  PELOriginalSchemePointGroup318.pull τ hτ ρ (parameterMap τ hτ ρ) pullback.condition.symm
abbrev quotient := classMap (parameterMap τ hτ ρ)
@[expose] def relativeValue (a : Points τ hτ T ρ) : TestClass (π τ hτ) ρ :=
  quotient τ hτ ρ (value τ hτ (totalBase τ hτ ρ) (original τ hτ ρ+parameter τ hτ ρ a)*
    (value τ hτ (totalBase τ hτ ρ) (original τ hτ ρ))⁻¹)
lemma parameter_class (a : Points τ hτ T ρ) :
    value τ hτ (totalBase τ hτ ρ) (parameter τ hτ ρ a)=
      LineClassPullbackHom318.pullback (parameterMap τ hτ ρ) (value τ hτ ρ a) := by
  exact LineClassPullbackLaws318.pullback_composition (parameterMap τ hτ ρ) a.val (classOf (line τ hτ))
lemma parameter_trivial (a : Points τ hτ T ρ) :
    quotient τ hτ ρ (value τ hτ (totalBase τ hτ ρ) (parameter τ hτ ρ a))=1 := by
  rw [parameter_class]
  exact base_class_trivial (parameterMap τ hτ ρ) (value τ hτ ρ a)
lemma zero_trivial : quotient τ hτ ρ (value τ hτ (totalBase τ hτ ρ) 0)=1 := by
  simpa only [map_zero] using parameter_trivial τ hτ ρ 0
lemma relativeValue_zero : relativeValue τ hτ ρ 0=1 := by
  simp only [relativeValue,map_zero,add_zero,mul_inv_cancel,map_one]

/-- UNIVERSAL relative additivity. The genuine cube line identity is
pulled back to X×T; its three parameter-only terms and zero term vanish
in the ACTUAL base-line quotient. No reducedness or field assumption on
T, no fppf halving and no pointwise-to-family inference are used. -/
theorem relativeValue_add (a b : Points τ hτ T ρ) :
    relativeValue τ hτ ρ (a+b)=relativeValue τ hτ ρ a*relativeValue τ hτ ρ b := by
  have h := congrArg (quotient τ hτ ρ)
    (cube τ hτ (totalBase τ hτ ρ) (original τ hτ ρ) (parameter τ hτ ρ a) (parameter τ hτ ρ b))
  have hab := parameter_trivial τ hτ ρ (a+b)
  rw [map_add] at hab
  simp only [map_mul,parameter_trivial,zero_trivial,hab,mul_one] at h
  rw [add_assoc] at h
  simp only [relativeValue,map_add,map_mul,map_inv]
  calc
    _ = (quotient τ hτ ρ (value τ hτ (totalBase τ hτ ρ)
          (original τ hτ ρ+(parameter τ hτ ρ a+parameter τ hτ ρ b)))*
        quotient τ hτ ρ (value τ hτ (totalBase τ hτ ρ) (original τ hτ ρ)))*
        (quotient τ hτ ρ (value τ hτ (totalBase τ hτ ρ) (original τ hτ ρ)))⁻¹*
        (quotient τ hτ ρ (value τ hτ (totalBase τ hτ ρ) (original τ hτ ρ)))⁻¹ := by group
    _ = _ := by rw [h]; group

@[expose] def hom : Multiplicative (Points τ hτ T ρ) →* TestClass (π τ hτ) ρ where
  toFun a := relativeValue τ hτ ρ a.toAdd
  map_one' := relativeValue_zero τ hτ ρ
  map_mul' a b := relativeValue_add τ hτ ρ a.toAdd b.toAdd

/-- Exact agreement with the original geometric Abel family. This
identifies the homomorphism with the existing natural transformation's
actual presheaf value before any sheafification is applied. -/
lemma family_value (a : Points τ hτ T ρ) :
    testMap (π τ hτ) (π τ hτ) ρ a.val a.property
      (classMap (PELOriginalTranslationDifferenceFamily318.second τ hτ)
        (classOf (PELOriginalTranslationDifferenceFamily318.family τ hτ)))=
      relativeValue τ hτ ρ a := by
  rw [testMap_class]
  have h : LineClassPullbackHom318.pullback (totalMap (π τ hτ) (π τ hτ) ρ a.val a.property)
      (classOf (PELOriginalTranslationDifferenceFamily318.family τ hτ))=
      value τ hτ (totalBase τ hτ ρ) (original τ hτ ρ+parameter τ hτ ρ a)*
        (value τ hτ (totalBase τ hτ ρ) (original τ hτ ρ))⁻¹ := by
    have he := classOf_eq (PELOriginalTranslationDifferenceFamily318.testIso τ hτ
      (original τ hτ ρ).val (parameter τ hτ ρ a).val
      ((original τ hτ ρ).property.trans (parameter τ hτ ρ a).property.symm))
    rw [LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse] at he
    exact he
  exact congrArg (quotient τ hτ ρ) h
end PELOriginalRelativePolarizationHom318
