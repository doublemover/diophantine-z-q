module
public import ActualTZHybridMaskMean318
public section
noncomputable section
namespace ActualTZHybridZeroOneTwoMean318
open Filter MeasureTheory
open scoped Topology BigOperators
open ActualTZHybridGlobalLocalStencil318 (Bits Axis)
open ActualTZHybridOrderedMeaning318 (mixed)
open ActualTZHybridCanonicalWrap318 (Context)
open ActualTZHybridMeanRate318 (scales)
open ActualTZHybridMaskMean318 (ν raw raw_eq_mixed all_masks)
open ActualTZLiteralSchwartz318 ActualTZLiteralOrdinaryBound318
variable {a s : ℕ}

private theorem rank_bound (t : Fin 3) :
    (Fintype.card (Bits a t.val):ℝ)≤(2:ℝ)^(a+2:ℕ) := by
  have ht : t.val≤2 := by omega
  have H : (Fintype.card (Bits a t.val):ℕ)≤2^(a+2) := by
    simp only [Bits,Axis,Fintype.card_fun,Fintype.card_bool,Fintype.card_sum,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)
  exact_mod_cast H

/-- The literal 0/1/2 hybrid contract. The minimum length, wrap-cap
ledger and frequency exponent are fixed before y,N; the eventual N
threshold precedes the choice of t, exact context and signed
ordinary-mask input. The underlying ν is the actual old cutoff
weight at the same n,b, not a centered ray-pseudorandomness input. -/
theorem both_local_blocks
    (C : Cutoff) (hχ : (∫ x in (0:ℝ)..1,|deriv C.χ x|^2)=1)
    (B σ : ℝ) (hB : ∀ x,|C.χ x|≤B) (hσ : 0<σ) (D : ℕ)
    (cap : Fin 3→ℕ) (l : ℕ→ℝ) (hl : ∀ y,0<l y)
    (hRank : 8*(2:ℝ)^(a+2:ℕ)*σ<1) :
    ∃ E : ℕ→ℝ,Tendsto E atTop (𝓝 0)∧(∀ y,0≤E y)∧
      ∃ y₀ : ℕ,∀ y≥y₀,∀ ε>0,∃ N₀ : ℕ,∀ N≥N₀,∀ t : Fin 3,
        ∀ (X : Context a t.val s (Bits a t.val)),scales X y N (l y)→X.cap=cap t→
          X.q≤(primorial y)^D→X.site=id→∀ m : Bits a t.val→Bool,
          |mixed (J:=X.J) (M:=X.M) X.hn X.q X.actualSlope
            (fun w x=>if m w then ν X (α (primorial y)) ((X.n:ℝ)^σ) C.χ x else 1)-1|≤E y+ε := by
  classical
  let P (t : Fin 3) (y N : ℕ) (η : ℝ) :=
    ∀ (X : Context a t.val s (Bits a t.val)),scales X y N (l y)→X.cap=cap t→
      X.q≤(primorial y)^D→∀ m : Bits a t.val→Bool,
      |raw X m (α (primorial y)) ((X.n:ℝ)^σ) C.χ-1|≤η
  have h (t : Fin 3) : ∃ e : ℕ→ℝ,Tendsto e atTop (𝓝 0)∧(∀ y,0≤e y)∧
      ∃ y₀ : ℕ,∀ y≥y₀,∀ ε>0,∃ N₀ : ℕ,∀ N≥N₀,P t y N (e y+ε) := by
    have hR : 8*(Fintype.card (Bits a t.val):ℝ)*σ<1 :=
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rank_bound (a:=a) t) (by norm_num)) hσ.le).trans_lt hRank
    exact all_masks (I:=Bits a t.val) (a:=a) (t:=t.val) (s:=s) C hχ B σ hB hσ D (cap t) hR l hl
  let e (t : Fin 3) := Classical.choose (h t)
  have he (t : Fin 3) := Classical.choose_spec (h t)
  have hP (t : Fin 3) (y N : ℕ) {u v : ℝ} (huv : u≤v) (H : P t y N u) : P t y N v :=
    fun X hy hc hq m=>(H X hy hc hq m).trans huv
  obtain ⟨E,hT,hE,y₀,hY⟩ :=
    ActualTZFiniteCutoffUniformity318.finite_rate P e (fun t=>(he t).1)
      (fun t=>(he t).2.1) hP (fun t=>(he t).2.2)
  refine ⟨E,hT,hE,y₀,?_⟩
  intro y hy ε hε
  obtain ⟨N₀,hN⟩ := hY y hy ε hε
  refine ⟨N₀,?_⟩
  intro N hn t X hS hc hQ hSite m
  rw [←raw_eq_mixed X hSite]
  exact hN N hn t X hS hc hQ m

end ActualTZHybridZeroOneTwoMean318
