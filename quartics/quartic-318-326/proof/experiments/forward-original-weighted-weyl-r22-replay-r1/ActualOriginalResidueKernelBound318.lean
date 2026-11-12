module
public import ActualOriginalQuadraticGauss318
public section
noncomputable section
namespace ActualOriginalResidueKernelBound318
open ActualOriginalQuadraticGauss318
set_option maxHeartbeats 16000000

lemma actual_kernel_value_dvd (q k : ℕ) [NeZero q] (x : ZMod q)
    (hx : (k : ZMod q)*x=0) : q ∣ k*x.val := by
  apply (ZMod.natCast_eq_zero_iff (k*x.val) q).mp
  simpa only [Nat.cast_mul,ZMod.natCast_val] using hx

/-- The actual kernel of multiplication by a positive integer k has at
most k residues for every nonzero modulus, with no primality/coprimality
assumption. Its injection sends x to k*x.val/q in the literal interval[0,k). -/
theorem actual_integer_kernel_card_bound (q k : ℕ) [NeZero q] (hk : 0 < k) :
    kernelCard q (k : ZMod q) ≤ k := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let f : {x : ZMod q // (k : ZMod q)*x=0} → Fin k := fun x =>
    ⟨k*x.val.val/q,(Nat.div_lt_iff_lt_mul hq).mpr
      (Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x.val) hk)⟩
  have hf : Function.Injective f := by
    intro x y he
    have heq : k*x.val.val/q = k*y.val.val/q := congrArg Fin.val he
    have hx : (k*x.val.val/q)*q = k*x.val.val :=
      Nat.div_mul_cancel (actual_kernel_value_dvd q k x.val x.prop)
    have hy : (k*y.val.val/q)*q = k*y.val.val :=
      Nat.div_mul_cancel (actual_kernel_value_dvd q k y.val y.prop)
    have hm : k*x.val.val = k*y.val.val := by rw [←hx,←hy,heq]
    apply Subtype.ext
    apply ZMod.val_injective
    exact mul_left_cancel₀ (Nat.ne_of_gt hk) hm
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin,Fintype.card_subtype,kernelCard] using hc

/-- A unit numerator changes no degeneracy kernel. The bound remains
valid at even and bad-prime moduli and at modulus1. -/
lemma actual_unit_quadratic_kernel_bound (q k : ℕ) [NeZero q] (hk : 0 < k)
    (a : ZMod q) (ha : IsUnit a) : kernelCard q (2*(a*(k : ZMod q))) ≤ 2*k := by
  classical
  have hp (h : ZMod q) : 2*(a*(k : ZMod q))*h=0 ↔ ((2*k : ℕ) : ZMod q)*h=0 := by
    have he : 2*(a*(k : ZMod q))*h = a*(((2*k : ℕ) : ZMod q)*h) := by
      push_cast
      ring
    rw [he]
    constructor
    · intro hzero
      apply ha.mul_left_cancel
      simpa only [mul_zero] using hzero
    · intro hzero
      rw [hzero,mul_zero]
  have he : kernelCard q (2*(a*(k : ZMod q))) = kernelCard q ((2*k : ℕ) : ZMod q) := by
    simp only [kernelCard,hp]
  rw [he]
  exact actual_integer_kernel_card_bound q (2*k) (by omega)

end ActualOriginalResidueKernelBound318
