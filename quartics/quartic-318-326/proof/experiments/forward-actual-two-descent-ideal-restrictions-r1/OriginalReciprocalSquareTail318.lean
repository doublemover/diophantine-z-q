module
public import OriginalAnisotropicResidueFibers318
public section
noncomputable section
namespace OriginalReciprocalSquareTail318
open scoped BigOperators
set_option maxHeartbeats 3000000

lemma reciprocal_step (x : ℝ) (hx : 0<x) :
    1/(x+1)^2≤1/x-1/(x+1) := by
  have hx1 : 0<x+1 := by linarith
  calc
    1/(x+1)^2≤1/(x*(x+1)) :=
      one_div_le_one_div_of_le (mul_pos hx hx1) (by nlinarith)
    _ = 1/x-1/(x+1) := by field_simp [hx.ne',hx1.ne']; ring

/-- Explicit finite telescoping, with the upper-end correction retained. -/
theorem reciprocal_prefix (P K : ℕ) (hP : 0<P) :
    ∑ i ∈ Finset.range K, 1/((P:ℝ)+(i:ℝ)+1)^2≤1/(P:ℝ)-1/((P:ℝ)+(K:ℝ)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have hx : 0<(P:ℝ)+(K:ℝ) := by positivity
      have hs := reciprocal_step ((P:ℝ)+(K:ℝ)) hx
      have hh := add_le_add ih hs
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_succ] at hh ⊢
      linarith

/-- Any finite set of DISTINCT natural moduli above P has reciprocal-
square mass at most1/P. Primality is not smuggled in as a distribution
estimate; the result applies to the actual retained prime set directly. -/
theorem finite_reciprocal_tail (P : ℕ) (hP : 0<P) (S : Finset ℕ)
    (hS : ∀ p∈S, P<p) : ∑ p∈S, 1/(p:ℝ)^2≤1/(P:ℝ) := by
  classical
  let T := S.image (fun p => p-P-1)
  let K := T.sup id+1
  have hinj : Set.InjOn (fun p : ℕ => p-P-1) (S : Set ℕ) := by
    intro p hp q hq he
    have hp' := hS p hp
    have hq' := hS q hq
    omega
  have he : ∑ i∈T, 1/((P:ℝ)+(i:ℝ)+1)^2=∑ p∈S, 1/(p:ℝ)^2 := by
    rw [Finset.sum_image (fun p hp q hq h => hinj hp hq h)]
    apply Finset.sum_congr rfl
    intro p hp
    have hh : P+(p-P-1)+1=p := by have hh := hS p hp;omega
    have hh' : (P:ℝ)+((p-P-1:ℕ):ℝ)+1=(p:ℝ) := by exact_mod_cast hh
    rw [hh']
  have hsub : T⊆Finset.range K := by
    intro i hi
    have hh : i≤T.sup id := Finset.le_sup (f := id) hi
    apply Finset.mem_range.mpr
    dsimp [K]
    omega
  have hs : ∑ i∈T, 1/((P:ℝ)+(i:ℝ)+1)^2≤
      ∑ i∈Finset.range K, 1/((P:ℝ)+(i:ℝ)+1)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rw [he] at hs
  have hpref := reciprocal_prefix P K hP
  have hn : 0≤1/((P:ℝ)+(K:ℝ)) := by positivity
  linarith

end OriginalReciprocalSquareTail318
