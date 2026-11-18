module
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic
public section
noncomputable section
namespace OrbitValueFixedField318
variable {G X:Type*} [Group G] (f:G→X)
variable (hf:∀ (t a b:G),f a=f b → f (t*a)=f (t*b))

/-- Stabilizer of a concretely evaluated orbit value; no normality is assumed. -/
def stabilizer : Subgroup G where
  carrier := {a | f a=f 1}
  one_mem' := rfl
  mul_mem' {a b} ha hb := (by simpa using hf a b 1 hb : f (a*b)=f a) |>.trans ha
  inv_mem' {a} ha := (by simpa using hf a⁻¹ a 1 ha : f 1=f a⁻¹).symm

theorem index [Finite X] : (stabilizer f hf).index ≤ Nat.card X := by
  let J := stabilizer f hf
  have rel (a b:G) : a⁻¹*b∈J ↔ f a=f b := by
    change f (a⁻¹*b)=f 1 ↔ _
    constructor
    · intro h
      simpa [←mul_assoc] using (hf a _ _ h).symm
    · intro h
      simpa using hf a⁻¹ b a h.symm
  let v : G ⧸ J → X := Quotient.lift f (fun a b hab =>
    (rel a b).mp (QuotientGroup.leftRel_apply.mp hab))
  have hi : Function.Injective v := by
    rintro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        intro hab
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((rel a b).mpr hab))
  exact Nat.card_le_card_of_injective v hi

/-- This is the true relative degree of the fixed field, not a degree
premise or a requirement that the orbit stabilizer be normal. -/
theorem finrank_fixed {k L:Type*} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L] (J:Subgroup (L≃ₐ[k]L)) :
    Module.finrank k (IntermediateField.fixedField J)=J.index := by
  have hh := Module.finrank_mul_finrank k (IntermediateField.fixedField J) L
  rw [IntermediateField.finrank_fixedField_eq_card] at hh
  have hcard : Nat.card (L≃ₐ[k]L) = Module.finrank k L := IsGalois.card_aut_eq_finrank k L
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hh.trans (J.index_mul_card.trans hcard).symm)

end OrbitValueFixedField318
