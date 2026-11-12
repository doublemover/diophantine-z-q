module
public import ActualOriginalResidueFourierLift318
public section
noncomputable section
namespace ActualOriginalNonunitFrequency318
open QuadricCRTAssembly318 ActualOriginalResidueFourierLift318
open scoped BigOperators
set_option maxHeartbeats 16000000

@[expose] def scaledFrequency (m p : ℕ) (a : ZMod m) : ZMod (m*p) :=
  (p : ZMod (m*p))*(a.val : ZMod (m*p))

lemma scaledFrequency_val (m p : ℕ) [NeZero m] [NeZero p] (a : ZMod m) :
    (scaledFrequency m p a).val=p*a.val := by
  simp only [scaledFrequency,←Nat.cast_mul]
  apply ZMod.val_natCast_of_lt
  have ha := a.val_lt
  have hp := NeZero.pos p
  nlinarith

/-- Exact image of multiplication-by-p frequencies, with the unique
base frequency recovered by division of the standard representative. -/
@[expose] def divisibleFrequencyEquiv (m p : ℕ) [NeZero m] [NeZero p] :
    ZMod m ≃ {a : ZMod (m*p) // p ∣ a.val} where
  toFun a := ⟨scaledFrequency m p a,by rw [scaledFrequency_val]; exact dvd_mul_right p a.val⟩
  invFun a := (a.val.val/p : ℕ)
  left_inv a := by
    rw [scaledFrequency_val,Nat.mul_div_right a.val (NeZero.pos p)]
    exact ZMod.natCast_zmod_val a
  right_inv a := by
    apply Subtype.ext
    apply ZMod.val_injective (m*p)
    rw [scaledFrequency_val,ZMod.val_natCast]
    have hlt : a.val.val/p<m := by
      apply (Nat.div_lt_iff_lt_mul (NeZero.pos p)).mpr
      simpa only [mul_comm] using a.val.val_lt
    rw [Nat.mod_eq_of_lt hlt,Nat.mul_div_cancel' a.property]

lemma prime_nonunit_iff (p n : ℕ) (hp : p.Prime) (a : ZMod (p^n*p)) :
    ¬IsUnit a ↔ p ∣ a.val := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hi := ZMod.isUnit_natCast_iff_not_dvd_pow (a:=a.val) hp (Nat.succ_pos n)
  rw [pow_succ] at hi
  rw [ZMod.natCast_zmod_val] at hi
  simp only [hi,not_not]

@[expose] def nonunitFrequencyEquiv (p n : ℕ) [NeZero p] (hp : p.Prime) :
    ZMod (p^n) ≃ {a : ZMod (p^n*p) // ¬IsUnit a} :=
  (divisibleFrequencyEquiv (p^n) p).trans
    ((Equiv.refl (ZMod (p^n*p))).subtypeEquiv (fun a => (prime_nonunit_iff p n hp a).symm))

lemma nonunitFrequencyEquiv_val (p n : ℕ) [NeZero p] (hp : p.Prime) (a : ZMod (p^n)) :
    (nonunitFrequencyEquiv p n hp a).val = scaledFrequency (p^n) p a := rfl

end ActualOriginalNonunitFrequency318
