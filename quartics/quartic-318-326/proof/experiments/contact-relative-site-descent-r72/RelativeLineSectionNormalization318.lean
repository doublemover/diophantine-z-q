module
public import RelativeLineClassQuotient318
public section
noncomputable section
namespace RelativeLineSectionNormalization318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open LineClassPullbackHom318 RelativeLineClassQuotient318
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X)

lemma section_pullback (section_eq : e ≫ p = 𝟙 S) (d : Class S) : pullback e (pullback p d) = d := by
  change LineSheafPullback318.pullback e (LineSheafPullback318.pullback p d) = d
  rw [← LineClassPullbackLaws318.pullback_composition, section_eq,
    LineClassPullbackLaws318.pullback_identity]

/-- Actual line-class normalization at the specified actual section: tensor by
the inverse of its pulled-back restriction. This is not degree normalization. -/
@[expose] def normalize : Class X →* Class X where
  toFun c := c * (pullback p (pullback e c))⁻¹
  map_one' := by simp
  map_mul' c d := by simp only [map_mul, mul_inv]; ac_rfl

lemma normalize_formula (c : Class X) :
    normalize p e c = c * (pullback p (pullback e c))⁻¹ := rfl

lemma normalize_at_section (section_eq : e ≫ p = 𝟙 S) (c : Class X) : pullback e (normalize p e c) = 1 := by
  rw [normalize_formula, map_mul, map_inv, section_pullback p e section_eq]
  exact mul_inv_cancel _

lemma normalize_base (section_eq : e ≫ p = 𝟙 S) (d : Class S) : normalize p e (pullback p d) = 1 := by
  rw [normalize_formula, section_pullback p e section_eq]
  exact mul_inv_cancel _

lemma normalize_fixed (c : Class X) (hc : pullback e c = 1) : normalize p e c = c := by
  rw [normalize_formula, hc, map_one, inv_one, mul_one]

/-- The original section-pullback kernel consists of classes with trivial
restriction to that section. It must not be called the degree-zero subgroup. -/
@[expose] def normalized (section_eq : e ≫ p = 𝟙 S) : Class X →* (pullback e).ker where
  toFun c := ⟨normalize p e c, normalize_at_section p e section_eq c⟩
  map_one' := Subtype.ext (map_one (normalize p e))
  map_mul' c d := Subtype.ext (map_mul (normalize p e) c d)

lemma base_in_kernel (section_eq : e ≫ p = 𝟙 S) : baseLines p ≤ (normalized p e section_eq).ker := by
  rintro c ⟨d, rfl⟩
  apply Subtype.ext
  exact normalize_base p e section_eq d

/-- The exact quotient by base lines maps to the kernel of the actual section
restriction, with no independent choice of a splitting homomorphism. -/
@[expose] def quotientToKernel (section_eq : e ≫ p = 𝟙 S) : RelativeClass p →* (pullback e).ker :=
  QuotientGroup.lift (baseLines p) (normalized p e section_eq) (base_in_kernel p e section_eq)

@[expose] def kernelToQuotient : (pullback e).ker →* RelativeClass p :=
  (classMap p).comp (pullback e).ker.subtype

lemma quotient_normalize (c : Class X) : classMap p (normalize p e c) = classMap p c := by
  rw [normalize_formula, map_mul, map_inv, base_class_trivial, inv_one, mul_one]

lemma kernel_left_inverse (section_eq : e ≫ p = 𝟙 S) (c : (pullback e).ker) :
    quotientToKernel p e section_eq (kernelToQuotient p e c) = c := by
  apply Subtype.ext
  exact normalize_fixed p e c.val c.property

lemma quotient_right_inverse (section_eq : e ≫ p = 𝟙 S) (c : RelativeClass p) :
    kernelToQuotient p e (quotientToKernel p e section_eq c) = c := by
  obtain ⟨d, rfl⟩ := classMap_surjective p c
  exact quotient_normalize p e d

/-- Exact equivalence with section-normalized original line classes. The
section is actual input; no rational section of the original source is assumed. -/
@[expose] def equivalence (section_eq : e ≫ p = 𝟙 S) : RelativeClass p ≃* (pullback e).ker where
  toFun := quotientToKernel p e section_eq
  invFun := kernelToQuotient p e
  left_inv := quotient_right_inverse p e section_eq
  right_inv := kernel_left_inverse p e section_eq
  map_mul' := map_mul (quotientToKernel p e section_eq)
end RelativeLineSectionNormalization318
