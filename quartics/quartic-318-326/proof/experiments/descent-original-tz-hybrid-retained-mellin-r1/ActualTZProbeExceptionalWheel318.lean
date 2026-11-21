module
public import Mathlib
public section
noncomputable section
namespace ActualTZProbeExceptionalWheel318
open scoped BigOperators

/-- Any exact *difference* of integer evaluations detects a
surviving marker. One need not divide a diagonal probe by two
or bound a chosen abstract coefficient through an l¹ norm. -/
theorem nonzero_from_probe {ι : Type*} (p : ℕ) (F : MvPolynomial ι ℤ) (x y : ι→ℤ)
    (H : ¬(p:ℤ)∣MvPolynomial.eval x F-MvPolynomial.eval y F) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) F≠0 := by
  intro h
  have X := MvPolynomial.map_eval (Int.castRingHom (ZMod p)) x F
  have Y := MvPolynomial.map_eval (Int.castRingHom (ZMod p)) y F
  rw [h,map_zero] at X Y
  apply H
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
  change Int.castRingHom (ZMod p) (MvPolynomial.eval x F-MvPolynomial.eval y F)=0
  rw [map_sub,X,Y,sub_zero]

/-- The actual old wheel is definitionally this primorial. The
pinned binomial proof avoids opening a new Chebyshev source proof. -/
theorem log_primorial (y : ℕ) : Real.log (primorial y:ℝ)≤Real.log 4*(y:ℝ) := by
  have H : (primorial y:ℝ)≤(4:ℝ)^y := by exact_mod_cast primorial_le_four_pow y
  have hp : 0<(primorial y:ℝ) := by exact_mod_cast primorial_pos y
  refine (Real.log_le_log hp H).trans_eq ?_
  rw [Real.log_pow,mul_comm]

variable {J : Type*} [Fintype J]

def exceptionalKey (c : J→ℤ) : ℕ := ∏ i : J,(c i).natAbs

theorem exceptional_pos (c : J→ℤ) (hc : ∀ i,c i≠0) : 0<exceptionalKey c := by
  unfold exceptionalKey
  apply Finset.prod_pos
  intro i _
  exact Nat.pos_of_ne_zero (fun he=>hc i (Int.natAbs_eq_zero.mp he))

theorem survives (c : J→ℤ) (p : ℕ) (h : ¬p∣exceptionalKey c) (i : J) :
    ¬(p:ℤ)∣c i := by
  intro H
  apply h
  have hD : p∣(c i).natAbs := by
    rw [←Int.natCast_dvd_natCast,Int.dvd_natAbs]
    exact H
  exact hD.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

/-- Uniform exceptional log loss from true finite coefficient or
probe height on the *actual* wheel. The hypothesis is intentionally
on the chosen signed nonzero marks, not on an arbitrary pole. -/
theorem log_key_with_wheel (y D : ℕ) (hy : 1≤y) (A : ℝ) (hA : 1≤A)
    (c : J→ℤ) (hc : ∀ i,c i≠0) (hSize : ∀ i,((c i).natAbs:ℝ)≤A*(primorial y:ℝ)^D) :
    Real.log (exceptionalKey c:ℝ)≤
      (Fintype.card J:ℝ)*(Real.log A+(D:ℝ)*Real.log 4)*(y:ℝ) := by
  have hW : 0<(primorial y:ℝ) := by exact_mod_cast primorial_pos y
  have hK : 0<(exceptionalKey c:ℝ) := by exact_mod_cast exceptional_pos c hc
  have hA0 : 0<A := zero_lt_one.trans_le hA
  have hKle : (exceptionalKey c:ℝ)≤(A*(primorial y:ℝ)^D)^Fintype.card J := by
    unfold exceptionalKey
    push_cast
    calc
      _ ≤ ∏ _ : J,A*(primorial y:ℝ)^D :=
        Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun i _=>hSize i)
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ]
  have h := Real.log_le_log hK hKle
  rw [Real.log_pow,Real.log_mul hA0.ne' (pow_ne_zero D hW.ne'),Real.log_pow] at h
  have hD := mul_le_mul_of_nonneg_left (log_primorial y) (Nat.cast_nonneg D)
  have hyR : (1:ℝ)≤y := by exact_mod_cast hy
  have hLog := mul_le_mul_of_nonneg_left hyR (Real.log_nonneg hA)
  calc
    _ ≤ (Fintype.card J:ℝ)*(Real.log A+(D:ℝ)*Real.log (primorial y:ℝ)) := h
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (Fintype.card J))
      nlinarith only [hD,hLog]

end ActualTZProbeExceptionalWheel318
