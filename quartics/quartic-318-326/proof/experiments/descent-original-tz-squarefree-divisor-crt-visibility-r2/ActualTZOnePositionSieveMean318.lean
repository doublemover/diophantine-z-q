module
public import ActualTZOneLinearDivisorCRT318
public import ActualTZOneDivisorExpansion318
import all ActualTZOneLinearDivisorCRT318
import all ActualTZOneDivisorExpansion318
public section
noncomputable section
namespace ActualTZOnePositionSieveMean318
open scoped BigOperators
open ActualTZOneLinearDivisorCRT318 ActualTZOneDivisorExpansion318

def physical (W b : ℕ) (s a : ℤ) (t : ℕ) : ℤ :=
  (W:ℤ)*(s+(t:ℤ)+a)+(b:ℤ)

def cellMean (α R : ℝ) (χ : ℝ→ℝ) (W b L : ℕ) (s a : ℤ) : ℝ :=
  (∑ t∈Finset.range L,weightedSquare α R χ (physical W b s a t).natAbs)/(L:ℝ)

def finiteMain (α R : ℝ) (χ : ℝ→ℝ) (W : ℕ) : ℝ :=
  α*Real.log R*∑ d∈cut R,∑ e∈cut R, (coeff R χ d*coeff R χ e)*localDensity W (d.lcm e)

private theorem rotate {X Y Z : Type*} (S : Finset X) (A : Finset Y) (B : Finset Z)
    (f : X→Y→Z→ℝ) :
    (∑ x∈S,∑ y∈A,∑ z∈B,f x y z)=∑ y∈A,∑ z∈B,∑ x∈S,f x y z := by
  calc
    _ = ∑ y∈A,∑ x∈S,∑ z∈B,f x y z := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

/-- This reindex holds on one actual affine wrap cell. All cutoff and
Möbius signs are retained; no distribution theorem is used. -/
theorem exact_cell_mean (α R : ℝ) (χ : ℝ→ℝ) (W b L : ℕ) (s a : ℤ)
    (hR : 1<R) (hχ : ∀ t>1,χ t=0)
    (hvalid : ∀ t<L,physical W b s a t≠0) :
    cellMean α R χ W b L s a=α*Real.log R*
      ∑ d∈cut R,∑ e∈cut R,(coeff R χ d*coeff R χ e)*
        ((count W (d.lcm e) b L s a:ℝ)/(L:ℝ)) := by
  classical
  let f (t d e : ℕ) :=
    if ((d.lcm e:ℕ):ℤ)∣physical W b s a t then coeff R χ d*coeff R χ e else 0
  have h (t : ℕ) (ht : t∈Finset.range L) :
      weightedSquare α R χ (physical W b s a t).natAbs=
        α*Real.log R*∑ d∈cut R,∑ e∈cut R,f t d e := by
    have hp := Int.natAbs_pos.mpr (hvalid t (Finset.mem_range.mp ht))
    have he (q : ℕ) : q∣(physical W b s a t).natAbs ↔ (q:ℤ)∣physical W b s a t :=
      Int.natCast_dvd_natCast.symm.trans Int.dvd_natAbs
    simpa only [f,he] using double_squarefree α R χ (physical W b s a t).natAbs hp hR hχ
  have hfin (d e : ℕ) :
      (∑ t∈Finset.range L,f t d e)=
        (coeff R χ d*coeff R χ e)*(count W (d.lcm e) b L s a:ℝ) := by
    rw [Finset.mul_sum]
    simp only [count,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t _
    change (if ((d.lcm e:ℕ):ℤ)∣physical W b s a t then _ else _) =
      _ * ((if ((d.lcm e:ℕ):ℤ)∣physical W b s a t then (1:ℕ) else 0):ℝ)
    split_ifs <;> simp
  unfold cellMean
  rw [Finset.sum_congr rfl h,←Finset.mul_sum,rotate (Finset.range L) (cut R) (cut R) f,
    mul_div_assoc]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  rw [hfin,mul_div_assoc]

/-- Uniform elementary remainder, before the strictly separate
evaluation of the finite signed cutoff density. The bound has no
dependence on signed interval start, residue, or wrap cell. -/
theorem one_position_error (α R : ℝ) (χ : ℝ→ℝ) (W b L : ℕ) (s a : ℤ)
    (hR : 1<R) (hχ : ∀ t>1,χ t=0)
    (hvalid : ∀ t<L,physical W b s a t≠0)
    (hWb : W.Coprime b) (hL : 0<L)
    (C : ℝ) (hχBound : ∀ t,|χ t| ≤ C) :
    |cellMean α R χ W b L s a-finiteMain α R χ W| ≤
      |α*Real.log R|*((((⌊R⌋₊+1:ℕ):ℝ))^2*(C^2/(L:ℝ))) := by
  have hC : 0≤C := (abs_nonneg _).trans (hχBound 0)
  let E (d e : ℕ) :=
    (count W (d.lcm e) b L s a:ℝ)/(L:ℝ)-localDensity W (d.lcm e)
  let D (d e : ℕ) := coeff R χ d*coeff R χ e
  have hErr :
      (∑ d∈cut R,∑ e∈cut R,D d e*
        ((count W (d.lcm e) b L s a:ℝ)/(L:ℝ))) -
      (∑ d∈cut R,∑ e∈cut R,D d e*localDensity W (d.lcm e)) =
        ∑ d∈cut R,∑ e∈cut R,D d e*E d e := by
    simp only [E,mul_sub,Finset.sum_sub_distrib]
  rw [exact_cell_mean α R χ W b L s a hR hχ hvalid,finiteMain,←mul_sub,hErr,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hc : ((cut R).card:ℝ)≤((⌊R⌋₊+1:ℕ):ℝ) := by exact_mod_cast cut_card_le R
  calc
    _ ≤ ∑ d∈cut R,∑ e∈cut R, |D d e*E d e| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _d∈cut R,∑ _e∈cut R,C^2/(L:ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have hd' := cutoff_norm R χ d hd C hχBound
      have he' := cutoff_norm R χ e he C hχBound
      have hur := normalized_error W (d.lcm e) b L s a (Nat.lcm_pos (cut_pos hd) (cut_pos he)) hWb hL
      have hp : |D d e|≤C^2 := by
        rw [D,abs_mul,pow_two]
        exact mul_le_mul hd' he' (abs_nonneg _) hC
      rw [abs_mul]
      simpa only [mul_one_div] using mul_le_mul hp hur (abs_nonneg _) (sq_nonneg C)
    _ = ((cut R).card:ℝ)^2*(C^2/(L:ℝ)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hc 2) (by positivity)

/-- A finite signed cutoff density is nonnegative because it is a
finite complete-period average of the original real square. No
infinite rearrangement of signed Möbius coefficients is involved. -/
theorem finiteMain_nonneg (α R : ℝ) (χ : ℝ→ℝ) (W b : ℕ)
    (hα : 0≤α) (hR : 1<R) (hχ : ∀ t>1,χ t=0)
    (hW : 0<W) (hb : 0<b) (hWb : W.Coprime b) :
    0≤finiteMain α R χ W := by
  let Q := ∏ d∈cut R,∏ e∈cut R,d.lcm e
  have hQ : 0<Q := by
    apply Finset.prod_pos
    intro d hd
    apply Finset.prod_pos
    intro e he
    exact Nat.lcm_pos (cut_pos hd) (cut_pos he)
  have hValid (t : ℕ) (_ : t<Q) : physical W b 1 0 t≠0 := by
    apply ne_of_gt
    unfold physical
    positivity
  have hExact : cellMean α R χ W b Q 1 0=finiteMain α R χ W := by
    rw [exact_cell_mean _ _ _ _ _ _ _ _ hR hχ hValid,finiteMain]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    have hDQ : d.lcm e∣Q :=
      (Finset.dvd_prod_of_mem _ he).trans (Finset.dvd_prod_of_mem _ hd)
    rw [exact_full_period _ _ _ _ _ _ (Nat.lcm_pos (cut_pos hd) (cut_pos he)) hWb hQ hDQ]
  rw [←hExact,cellMean]
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro t _
  unfold weightedSquare
  exact mul_nonneg (mul_nonneg hα (Real.log_pos hR).le) (sq_nonneg _)

end ActualTZOnePositionSieveMean318
