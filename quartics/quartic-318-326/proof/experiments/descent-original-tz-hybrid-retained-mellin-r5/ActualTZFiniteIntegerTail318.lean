module
public import ActualTZPositiveEulerMajorant318
public section
noncomputable section
namespace ActualTZFiniteIntegerTail318
open scoped BigOperators
open ActualTZPositiveEulerMajorant318

/-- Exact nonnegative finite tail after a strict integer cutoff.
No prime density premise. p=N+1 is retained as the first term. -/
theorem tail (σ : ℝ) (hσ : 0<σ) (N : ℕ) (hN : 0<N)
    (S : Finset ℕ) (hS : ∀ p∈S,N<p) :
    (∑ p∈S,(p:ℝ)^(-1-σ))≤(N:ℝ)^(-σ)/σ := by
  let T := S.image (fun p=>p-(N+1))
  let f (n : ℕ) := ((n+N+1:ℕ):ℝ)^(-1-σ)
  have hj : Function.Injective (fun n : ℕ=>n+N+1) := by
    intro a b h
    omega
  have hSum : Summable f :=
    (Real.summable_nat_rpow.mpr (show (-1:ℝ)-σ< -1 by linarith)).comp_injective hj
  have he : (∑ n∈T,f n)=∑ p∈S,(p:ℝ)^(-1-σ) := by
    have hinj : Set.InjOn (fun p : ℕ=>p-(N+1)) ↑S := by
      intro a ha b hb he'
      have ha' := hS a ha
      have hb' := hS b hb
      omega
    rw [T,Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro p hp
    have H := hS p hp
    have he' : p-(N+1)+N+1=p := by omega
    rw [f,he']
  rw [←he]
  exact (hSum.sum_le_tsum T (fun _ _=>by dsimp only [f]; positivity)).trans (integer_tail σ hσ N hN)

end ActualTZFiniteIntegerTail318
