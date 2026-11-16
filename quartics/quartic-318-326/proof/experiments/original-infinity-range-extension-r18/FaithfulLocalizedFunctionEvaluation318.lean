module
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Data.Complex.Basic
public section
noncomputable section
namespace FaithfulLocalizedFunctionEvaluation318
variable {A X : Type*} [CommRing A] [Algebra ℂ A]
variable (f : A →ₐ[ℂ] (X → ℂ)) (d : A) (hd : ∀ x, f d x ≠ 0)

/-- Pointwise reciprocal is used only where the actual denominator is nowhere zero. -/
def denominatorUnit : IsUnit (f d) := by
  refine ⟨⟨f d,fun x => (f d x)⁻¹,?_,?_⟩,rfl⟩
  · funext x
    exact mul_inv_cancel₀ (hd x)
  · funext x
    exact inv_mul_cancel₀ (hd x)

@[expose] def evaluation : Localization.Away d →ₐ[ℂ] (X → ℂ) :=
  IsLocalization.Away.liftAlgHom (f := f) d (denominatorUnit f d hd)

lemma evaluation_source (a : A) :
    evaluation f d hd (algebraMap A (Localization.Away d) a) = f a := by
  simp [evaluation,IsLocalization.Away.liftAlgHom_apply]

/-- Every localized element has a single exact numerator and denominator power
on the WHOLE stated source, not merely pointwise chosen fractions. -/
theorem exists_ratio (a : Localization.Away d) :
    ∃ b : A, ∃ n : ℕ, ∀ x, evaluation f d hd a x = f b x / (f d x)^n := by
  obtain ⟨⟨b,s⟩,he⟩ := IsLocalization.surj (Submonoid.powers d) a
  obtain ⟨n,hn⟩ := s.property
  refine ⟨b,n,?_⟩
  intro x
  have h := congrArg (fun q => evaluation f d hd q x) he
  simp only [map_mul,evaluation_source,Pi.mul_apply] at h
  rw [←hn,map_pow,Pi.pow_apply] at h
  exact (eq_div_iff (pow_ne_zero n (hd x))).mpr h

/-- Faithfulness is proved from the original evaluator and localization
relations. The ambient function ring is not asserted to be a domain. -/
theorem evaluation_injective (hf : Function.Injective f) :
    Function.Injective (evaluation f d hd) := by
  suffices hz : ∀ a, evaluation f d hd a = 0 → a = 0 by
    intro a b h
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,h,sub_self]
  intro a ha
  obtain ⟨⟨b,s⟩,he⟩ := IsLocalization.surj (Submonoid.powers d) a
  have hb : b = 0 := by
    apply hf
    have h := congrArg (evaluation f d hd) he
    rw [map_mul,ha,zero_mul,evaluation_source] at h
    exact h.symm.trans (map_zero f).symm
  obtain ⟨u,hu⟩ := IsLocalization.map_units (Localization.Away d) s
  have hzero : a * (u : Localization.Away d) = 0 := by
    rw [hu,he,hb,map_zero]
  calc
    a = a * ((u : Localization.Away d) * ↑(u⁻¹)) := by simp
    _ = (a * (u : Localization.Away d)) * ↑(u⁻¹) := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hzero,zero_mul]
end FaithfulLocalizedFunctionEvaluation318
