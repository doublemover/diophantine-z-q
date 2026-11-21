module
public import ActualTZFiniteProductNearOne318
public import ActualTZReferenceFactorNearOne318
public section
noncomputable section
namespace ActualTZFiniteMovingReference318
open scoped BigOperators
open ActualTZFiniteProductNearOne318 ActualTZReferenceFactorNearOne318
open ActualTZMovingReferenceTail318 ActualTZPositiveEulerMajorant318

variable {I : Type*} [Fintype I]

/-- All factors omitted at P=N+1, in their translated integer
indices. The bound is uniform in every angular coordinate, with
a linear 7|I| constant rather than independent position bounds
multiplied after estimating the error. -/
theorem shifted_finite_tail (L : ℝ) (hL : 0<L) (N : ℕ)
    (hN : Real.exp (L^2)≤(N:ℝ)) (S : Finset ℕ)
    (hS : ∀ n∈S,(n+N+1).Prime) (s t : I→ℂ)
    (hs : ∀ i,1/L≤(s i).re) (ht : ∀ i,1/L≤(t i).re) :
    ‖(∏ n∈S,∏ i : I,B (n+N+1) (s i) (t i))-1‖≤
      Real.exp (7*(Fintype.card I:ℝ)*(L*Real.exp (-L)))-1 := by
  classical
  have hσ : 0<(1:ℝ)/L := by positivity
  let f (n : ℕ) := q (1/L) (n+N+1)
  have hsum : Summable f := by
    have H := Real.summable_nat_rpow.mpr (show (-1:ℝ)-1/L< -1 by linarith)
    have hinj : Function.Injective (fun n : ℕ => n+N+1) := by
      intro a b h
      omega
    exact H.comp_injective hinj
  have hNon (n : ℕ) : 0≤f n := by dsimp only [f,q]; positivity
  have hTail : (∑ n∈S,f n)≤L*Real.exp (-L) :=
    (hsum.sum_le_tsum S (fun n _ => hNon n)).trans (raw_tail L hL N hN)
  let T := S ×ˢ (Finset.univ : Finset I)
  have H :
      ‖(∏ z∈T,B (z.1+N+1) (s z.2) (t z.2))-1‖≤
        Real.exp (∑ z∈T,7*f z.1)-1 := by
    apply product_near_one
    intro z hz
    have h := (Finset.mem_product.mp hz).1
    exact at_regulator (1/L) hσ _ (hS z.1 h) _ _ (hs z.2) (ht z.2)
  simp only [T,Finset.prod_product,Finset.sum_product,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul] at H
  apply H.trans
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  calc
    _ = (7*(Fintype.card I:ℝ))*(∑ n∈S,f n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hTail (by positivity)

/-- Shift back to actual primes N<p. No prime at p=N+1 is lost. -/
theorem omitted_finite_tail (L : ℝ) (hL : 0<L) (N : ℕ)
    (hN : Real.exp (L^2)≤(N:ℝ)) (P : ℕ)
    (s t : I→ℂ) (hs : ∀ i,1/L≤(s i).re) (ht : ∀ i,1/L≤(t i).re) :
    ‖(∏ p∈(Nat.primesBelow P).filter (fun p => N<p),
        ∏ i : I,B p (s i) (t i))-1‖≤
      Real.exp (7*(Fintype.card I:ℝ)*(L*Real.exp (-L)))-1 := by
  classical
  let T := (Nat.primesBelow P).filter (fun p => N<p)
  let S := T.image (fun p => p-(N+1))
  have hNle (p : ℕ) (hp : p∈T) : N+1≤p := (Finset.mem_filter.mp hp).2
  have hi : Set.InjOn (fun p : ℕ => p-(N+1)) ↑T := by
    intro a ha b hb h
    have ha' := hNle a ha
    have hb' := hNle b hb
    omega
  have hS (n : ℕ) (hn : n∈S) : (n+N+1).Prime := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have H : p-(N+1)+N+1=p := by have h := hNle p hp; omega
    rw [H]
    exact Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
  have H := shifted_finite_tail L hL N hN S hS s t hs ht
  have hE : (∏ n∈S,∏ i : I,B (n+N+1) (s i) (t i))=
      ∏ p∈T,∏ i : I,B p (s i) (t i) := by
    rw [S,Finset.prod_image hi]
    apply Finset.prod_congr rfl
    intro p hp
    have H : p-(N+1)+N+1=p := by have h := hNle p hp; omega
    rw [H]
  exact hE ▸ H

end ActualTZFiniteMovingReference318
