module
public import ActualPrimitiveSourceRestriction318
public section
noncomputable section
namespace ActualPrimitiveNonnegativeSieve318
open scoped BigOperators
open QuadricCRTAssembly318 ActualPrimitiveSourceRestriction318 OriginalWeightedSelberg318
open ActualTruncatedSelbergEuler318
set_option maxHeartbeats 20000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Literal weighted fibers for an arbitrary actual nonnegative source
weight. This includes smooth majorants and the unweighted count without
silently identifying them with the product-log source weight. -/
@[expose] def fiberWeight (κ : ℤ) (γ : J → ℤ) (S : Finset (Quadric κ))
    (w : Quadric κ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑v∈S.filter (fun v => key κ γ v=n),w v

lemma actual_fiber_event (κ : ℤ) (γ : J → ℤ) (S : Finset (Quadric κ))
    (w : Quadric κ → ℝ) (E : ℕ → Prop) [DecidablePred E] :
    (∑n∈S.image (key κ γ),if E n then fiberWeight κ γ S w n else 0)=
      ∑v∈S,if E (key κ γ v) then w v else 0 := by
  classical
  calc
    _ = ∑n∈S.image (key κ γ),∑v∈S.filter (fun v => key κ γ v=n),
        if E (key κ γ v) then w v else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases he : E n
      · simp only [he,ite_true,fiberWeight]
        apply Finset.sum_congr rfl
        intro v hv
        simp only [(Finset.mem_filter.mp hv).2,he,ite_true]
      · simp only [he,ite_false]
        symm
        apply Finset.sum_eq_zero
        intro v hv
        simp only [(Finset.mem_filter.mp hv).2,he,ite_false]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun v hv => Finset.mem_image_of_mem (key κ γ) hv) _

/-- Actual SAME local sieve with a genuine chosen nonnegative weight on
the globally primitive original source. Nothing assumes an asymptotic
for these weights; the remainder is recomputed from these exact fibers. -/
@[expose] def sieve (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ)
    (S : Finset (Quadric κ)) (w : Quadric κ → ℝ) (hw : ∀v,0≤w v) : BoundingSieve := by
  classical
  exact { ActualRemovedSelbergSieve318.sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded (primitiveSource κ S) with
    weights := fiberWeight κ γ (primitiveSource κ S) w
    weights_nonneg := fun n => Finset.sum_nonneg (fun v _ => hw v)
    totalMass := ∑v∈primitiveSource κ S,w v }

lemma actual_sifted_sum (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ)
    (S : Finset (Quadric κ)) (w : Quadric κ → ℝ) (hw : ∀v,0≤w v) :
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S w hw).siftedSum=
      ∑v∈primitiveSource κ S,if Nat.Coprime (product κ γ N excluded) (key κ γ v)
        then w v else 0 :=
  actual_fiber_event κ γ (primitiveSource κ S) w (Nat.Coprime (product κ γ N excluded))

/-- MainSum depends on the SAME nu and prime product, so the already
constructed optimal coefficients apply without replacing the actual
new weighted remainder by the old product-log remainder. -/
lemma actual_main_sum_identity (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded : ℕ) (S : Finset (Quadric κ)) (w : Quadric κ → ℝ)
    (hw : ∀v,0≤w v) (μ : ℕ → ℝ) :
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S w hw).mainSum μ=
      (ActualRemovedSelbergSieve318.sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded
        (primitiveSource κ S)).mainSum μ := rfl

end ActualPrimitiveNonnegativeSieve318
