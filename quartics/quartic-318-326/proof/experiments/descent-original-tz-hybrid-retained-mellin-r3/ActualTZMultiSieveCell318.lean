module
public import ActualTZMultiLinearCRT318
public import ActualTZMultiDivisorExpansion318
import all ActualTZMultiLinearCRT318
import all ActualTZOneDivisorExpansion318
public section
noncomputable section
namespace ActualTZMultiSieveCell318

open scoped BigOperators
open ActualTZOneDivisorExpansion318 ActualTZMultiDivisorExpansion318 ActualTZMultiLinearCRT318
variable {I : Type*} [Fintype I] [DecidableEq I]

def paired {R : ℝ} (d e : Assignment I R) (i : I×Bool) : ℕ :=
  if i.2 then (d i.1).val else (e i.1).val

theorem paired_squarefree {R : ℝ} (d e : Assignment I R) (i : I×Bool) :
    Squarefree (paired d e i) := by
  unfold paired
  split_ifs
  · exact (Finset.mem_filter.mp (d i.1).property).2
  · exact (Finset.mem_filter.mp (e i.1).property).2

def value (W : ℕ) (a : I→ℤ) (b : I→ℕ) (x : ℤ) (i : I) : ℤ :=
  (W:ℤ)*x+physicalConst W a b i

theorem paired_test {R : ℝ} (d e : Assignment I R) (W : ℕ) (a : I→ℤ) (b : I→ℕ)
    (x : ℤ) :
    (∀ i,(d i).val.lcm (e i).val∣(value W a b x i).natAbs) ↔
      Fits W (paired d e) (a ∘ Prod.fst) (b ∘ Prod.fst) x := by
  have hdvd (q : ℕ) (i : I) : q∣(value W a b x i).natAbs ↔ (q:ℤ)∣value W a b x i :=
    Int.natCast_dvd_natCast.symm.trans Int.dvd_natAbs
  constructor
  · intro h
    rintro ⟨i,bit⟩
    obtain ⟨h₁,h₂⟩ := Nat.lcm_dvd_iff.mp (h i)
    cases bit
    · simpa only [paired,Bool.false_eq_true,if_false,value,physicalConst,Function.comp_apply] using
        (hdvd _ i).mp h₂
    · simpa only [paired,if_pos (rfl : true=true),value,physicalConst,Function.comp_apply] using
        (hdvd _ i).mp h₁
  · intro h i
    apply Nat.lcm_dvd_iff.mpr
    exact ⟨(hdvd _ i).mpr (h (i,true)),(hdvd _ i).mpr (h (i,false))⟩

def assay (α R : ℝ) (χ : ℝ→ℝ) (W : ℕ) (a : I→ℤ) (b : I→ℕ) (L : ℕ) (s : ℤ) : ℝ :=
  (∑ t∈Finset.range L,∏ i : I,weightedSquare α R χ (value W a b (s+(t:ℤ)) i).natAbs)/(L:ℝ)

def finiteMain (α R : ℝ) (χ : ℝ→ℝ) (W : ℕ) (a : I→ℤ) (b : I→ℕ) : ℝ :=
  (α*Real.log R)^Fintype.card I * ∑ d : Assignment I R,∑ e : Assignment I R,
    amplitude R χ d e * jointDensity W (paired d e) (a ∘ Prod.fst) (b ∘ Prod.fst)

private theorem rotate {J : Type*} [Fintype J] (S : Finset ℕ) (f : ℕ→J→J→ℝ) :
    (∑ t∈S,∑ d : J,∑ e : J,f t d e)=∑ d : J,∑ e : J,∑ t∈S,f t d e := by
  calc
    _ = ∑ d : J,∑ t∈S,∑ e : J,f t d e := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

theorem exact_cell (α R : ℝ) (χ : ℝ→ℝ) (W : ℕ) (a : I→ℤ) (b : I→ℕ)
    (L : ℕ) (s : ℤ) (hR : 1<R) (hχ : ∀ t>1,χ t=0)
    (hn : ∀ t<L,∀ i,value W a b (s+(t:ℤ)) i≠0) :
    assay α R χ W a b L s =
      (α*Real.log R)^Fintype.card I * ∑ d : Assignment I R,∑ e : Assignment I R,
        amplitude R χ d e * ((jointCount W (paired d e) (a ∘ Prod.fst) (b ∘ Prod.fst) L s:ℝ)/(L:ℝ)) := by
  classical
  let f (t : ℕ) (d e : Assignment I R) :=
    if Fits W (paired d e) (a ∘ Prod.fst) (b ∘ Prod.fst) (s+(t:ℤ)) then amplitude R χ d e else 0
  have h (t : ℕ) (ht : t∈Finset.range L) :
      (∏ i : I,weightedSquare α R χ (value W a b (s+(t:ℤ)) i).natAbs) =
        (α*Real.log R)^Fintype.card I * ∑ d : Assignment I R,∑ e : Assignment I R,f t d e := by
    simpa only [f,paired_test] using product_expand α R χ
      (fun i => (value W a b (s+(t:ℤ)) i).natAbs)
      (fun i => Int.natAbs_pos.mpr (hn t (Finset.mem_range.mp ht) i)) hR hχ
  have hc (d e : Assignment I R) : (∑ t∈Finset.range L,f t d e)=
      amplitude R χ d e * (jointCount W (paired d e) (a ∘ Prod.fst) (b ∘ Prod.fst) L s:ℝ) := by
    rw [jointCount,Nat.cast_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    unfold f
    split_ifs <;> simp
  unfold assay
  rw [Finset.sum_congr rfl h,←Finset.mul_sum,rotate (Finset.range L) f,mul_div_assoc]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  rw [hc,mul_div_assoc]

/-- One actual jointly wrapped x-cell, with a signed bound uniform
over both divisor assignments, all original shifts and residues,
and all gcd/collision combinations at a fixed R. -/
theorem normalized_error (α R : ℝ) (χ : ℝ→ℝ) (W : ℕ) (a : I→ℤ) (b : I→ℕ)
    (L : ℕ) (s : ℤ) (hR : 1<R) (hχ : ∀ t>1,χ t=0)
    (hn : ∀ t<L,∀ i,value W a b (s+(t:ℤ)) i≠0)
    (hL : 0<L) (hUnit : ∀ i,W.Coprime (b i)) (C : ℝ) (hC : ∀ t,|χ t| ≤ C) :
    |assay α R χ W a b L s-finiteMain α R χ W a b| ≤
      |(α*Real.log R)^Fintype.card I|*
        (((((⌊R⌋₊+1:ℕ):ℝ))^(2*Fintype.card I))*(C^(2*Fintype.card I)/(L:ℝ))) := by
  let n := Fintype.card I
  let D := (⌊R⌋₊+1:ℕ)
  let e (d t : Assignment I R) :=
    (jointCount W (paired d t) (a ∘ Prod.fst) (b ∘ Prod.fst) L s:ℝ)/(L:ℝ)-
    jointDensity W (paired d t) (a ∘ Prod.fst) (b ∘ Prod.fst)
  rw [exact_cell α R χ W a b L s hR hχ hn,finiteMain,←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hx : (∑ d : Assignment I R,∑ t : Assignment I R,amplitude R χ d t*
      ((jointCount W (paired d t) (a ∘ Prod.fst) (b ∘ Prod.fst) L s:ℝ)/(L:ℝ))) -
    (∑ d : Assignment I R,∑ t : Assignment I R,amplitude R χ d t*
      jointDensity W (paired d t) (a ∘ Prod.fst) (b ∘ Prod.fst)) =
    ∑ d : Assignment I R,∑ t : Assignment I R,amplitude R χ d t*e d t := by
    simp only [e,mul_sub,Finset.sum_sub_distrib]
  rw [hx]
  have hCard : (Fintype.card (Assignment I R):ℝ)≤(D:ℝ)^n := by
    simp only [Assignment,Digit,Fintype.card_fun,Fintype.card_coe,Nat.cast_pow,D,n]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast cut_card_le R) _
  have hCC : 0≤C := (abs_nonneg _).trans (hC 0)
  have hLL : (0:ℝ)<L := by exact_mod_cast hL
  calc
    _ ≤ ∑ d : Assignment I R,∑ t : Assignment I R,|amplitude R χ d t*e d t| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _d : Assignment I R,∑ _t : Assignment I R,C^(2*n)/(L:ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro t _
      have ht : |e d t|≤1/(L:ℝ) := normalized_round W (paired d t)
        (a ∘ Prod.fst) (b ∘ Prod.fst) L s (paired_squarefree d t) (fun i => hUnit i.1) hL
      rw [abs_mul]
      simpa only [n,mul_one_div] using mul_le_mul (amplitude_bound R χ C hC d t)
        ht (abs_nonneg _) (pow_nonneg hCC _)
    _ = (Fintype.card (Assignment I R):ℝ)^2*(C^(2*n)/(L:ℝ)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ ((D:ℝ)^n)^2*(C^(2*n)/(L:ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hCard 2)
        (div_nonneg (pow_nonneg hCC _) hLL.le)
    _ = _ := by rw [←pow_mul,mul_comm n 2] <;> rfl

end ActualTZMultiSieveCell318
