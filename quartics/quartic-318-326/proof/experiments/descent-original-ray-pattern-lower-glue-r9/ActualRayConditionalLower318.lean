module
public import ActualRayInteriorMassRectangles318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualRayConditionalLower318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualRayLiteralInteriorWeight318
open ActualRayInteriorMassRectangles318 ActualRayConductorRows318 ActualRayPeriodicRectangle318

/-- Raw prime-log mass on the exact interior of this row; outside
positive primes in the prescribed rational ray the weight is zero. -/
@[expose] def rowRaw (r : Row) : ℝ :=
  rectangle (rawWeight r) (start r.n) 1 (width r.n) r.M

@[expose] def rowMean (r : Row) (F b c : ℕ) (μ : ℤ→ℝ) : ℝ :=
  ActualRayPeriodicRectangle318.mean
    (fold (table F r.k (d r) μ) F r.W b c) (r.W.lcm F/r.W)

/-- Every pointed mixed error is exactly the one in the nonlinear donor.
There is no sufficient 'linear existence' shortcut in this lemma. -/
theorem actual_row_error (r : Row) (hn : 0<r.n) (F b c : ℕ)
    (hW : 0<r.W) (hF : 0<F) (μ : ℤ→ℝ) (hμ : ∀ a, 0≤μ a ∧ μ a≤1)
    (hb : r.b=(b:ℤ)) (hc : r.c=(c:ℤ)) (hMean : ∀ a, r.mu a=μ (a%(F:ℤ)))
    (hwrap : ∀ z, dummy r z=1→∀ i<r.k, noWrap r i z)
    (hcut : ∀ z, dummy r z=1→∀ i<r.k,
      (r.cut:ℤ)≤baseIndex r z+shift r i (stepIndex r z))
    (eps : ℝ) (hMix : MixedBudget r (eps*(r.n:ℝ)*(r.M:ℝ))) :
    |r.phiRatio^r.k*rowRaw r-(width r.n:ℝ)*(r.M:ℝ)*rowMean r F b c μ| ≤
      (r.k:ℝ)*(eps*(r.n:ℝ)*(r.M:ℝ))+
        ((r.W.lcm F/r.W:ℕ):ℝ)*((width r.n:ℝ)+(r.M:ℝ)) := by
  let G := table F r.k (d r) μ
  let P := rectangle (fold G F r.W b c) (start r.n) 1 (width r.n) r.M
  have hT := total_of_mixed r (eps*(r.n:ℝ)*(r.M:ℝ)) hMix
  rw [prime_mass_exact r hn hwrap hcut,mean_mass_exact r hn F b c μ hb hc hMean hwrap] at hT
  have h₁ : |r.phiRatio^r.k*rowRaw r-P|≤(r.k:ℝ)*(eps*(r.n:ℝ)*(r.M:ℝ)) := hT
  have hR := fixed_conductor_row_error G F r.W b c hW hF (start r.n) 1
    (width r.n) r.M 1 (table_bounds F r.k (d r) μ hμ)
  have h₂ : |P-(width r.n:ℝ)*(r.M:ℝ)*rowMean r F b c μ|≤
      ((r.W.lcm F/r.W:ℕ):ℝ)*((width r.n:ℝ)+(r.M:ℝ)) := by
    simpa only [rowMean,G,P,mul_one] using hR
  calc
    _ = |(r.phiRatio^r.k*rowRaw r-P)+
        (P-(width r.n:ℝ)*(r.M:ℝ)*rowMean r F b c μ)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h₁ h₂)

/-- For fixed y then N, combine precisely the two separated analytic
sources: actual centered linear-cube bounds and the pointed nonlinear
transfer donor. The threshold in N may depend on fixed y. -/
theorem mixed_uniform_after_fixed_cutoff (H : Family) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ)
    (transfer : ActualDonor H a qMax jMin jMax)
    (cube : ∀ δ : ℝ, 0<δ → ∃ y₀ : ℕ, ∀ y≥y₀, ∃ N₀ : ℕ, ∀ N≥N₀,
      ∀ r∈H.rows y N, LinearBudget r a (qMax y) (jMin y N) (jMax y N) δ) :
    ∀ eps : ℝ, 0<eps → ∃ y₀ : ℕ, ∀ y≥y₀, ∃ N₀ : ℕ, ∀ N≥N₀,
      ∀ r∈H.rows y N, MixedBudget r (eps*(r.n:ℝ)*(r.M:ℝ)) := by
  intro eps heps
  obtain ⟨δ,hδ,y₁,ht⟩ := transfer eps heps
  obtain ⟨y₂,hc⟩ := cube δ hδ
  refine ⟨max y₁ y₂,?_⟩
  intro y hy
  obtain ⟨N₁,h₁⟩ := ht y ((le_max_left _ _).trans hy)
  obtain ⟨N₂,h₂⟩ := hc y ((le_max_right _ _).trans hy)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN r hr
  exact h₁ N ((le_max_left _ _).trans hN) r hr
    (h₂ N ((le_max_right _ _).trans hN) r hr)

/-- Only finite bookkeeping remains after the row estimates. The two
error allowances are distinct: pointed nonlinear transfer and exact
CRT boundary strips. The chosen 24/25 and 3/25 margins leave more than
1/10 of the fixed singular coefficient times N T. -/
theorem finite_lower {ι : Type*} (S : Finset ι) (R μ : ι→ℝ)
    (α : ℝ) (hα : 0<α) (k W : ℕ) (hW : 0<W)
    (nI M N T : ℕ) (Ss : ℝ) (hSs : 0<Ss)
    (transferError periodicError : ℝ)
    (hrow : ∀ j∈S, |α^k*R j-(nI:ℝ)*(M:ℝ)*μ j|≤transferError+periodicError)
    (hseries : (24/25:ℝ)*Ss≤ (∑ j∈S, μ j)/(α^k*(W:ℝ)^2))
    (harea : (3/25:ℝ)*((N:ℝ)*(T:ℝ))≤(nI:ℝ)*(M:ℝ)*(W:ℝ)^2)
    (ht : (S.card:ℝ)*transferError≤α^k*(Ss*((N:ℝ)*(T:ℝ)))/200)
    (hp : (S.card:ℝ)*periodicError≤α^k*(Ss*((N:ℝ)*(T:ℝ)))/200) :
    Ss*((N:ℝ)*(T:ℝ))/10≤∑ j∈S, R j := by
  let A := α^k*(Ss*((N:ℝ)*(T:ℝ)))
  have hαk : 0<α^k := pow_pos hα _
  have hW' : 0<(W:ℝ) := by exact_mod_cast hW
  have hA : 0≤A := by dsimp [A]; positivity
  have hs := (le_div_iff₀ (mul_pos hαk (pow_pos hW' 2))).mp hseries
  have hAllMeans : (72/625:ℝ)*A≤(nI:ℝ)*(M:ℝ)*(∑ j∈S, μ j) := by
    calc
      _=((24/25:ℝ)*Ss*α^k)*((3/25:ℝ)*((N:ℝ)*(T:ℝ))) := by dsimp [A]; ring
      _≤((24/25:ℝ)*Ss*α^k)*((nI:ℝ)*(M:ℝ)*(W:ℝ)^2) :=
        mul_le_mul_of_nonneg_left harea (by positivity)
      _=(nI:ℝ)*(M:ℝ)*(((24/25:ℝ)*Ss)*(α^k*(W:ℝ)^2)) := by ring
      _≤_ := mul_le_mul_of_nonneg_left hs (by positivity)
  have hSum : -(S.card:ℝ)*(transferError+periodicError)≤
      α^k*(∑ j∈S, R j)-(nI:ℝ)*(M:ℝ)*(∑ j∈S, μ j) := by
    simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
    calc
      _=(∑ _j∈S, -(transferError+periodicError)) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _≤_ := Finset.sum_le_sum fun j hj => (abs_le.mp (hrow j hj)).1
  have hE : (S.card:ℝ)*(transferError+periodicError)≤A/100 := by
    rw [mul_add]
    change (S.card:ℝ)*transferError+(S.card:ℝ)*periodicError≤A/100
    change (S.card:ℝ)*transferError≤A/200 at ht
    change (S.card:ℝ)*periodicError≤A/200 at hp
    linarith only [ht,hp]
  by_contra! hfail
  have hstrict := mul_lt_mul_of_pos_left hfail hαk
  apply (not_lt_of_ge ?_) hstrict
  calc
    _=A/10 := by dsimp [A]; ring
    _≤_ := by linarith only [hA,hAllMeans,hSum,hE]

/-- The uniform occupied-row scale gives the literal mixed-error
allowance. Choose eps from Z and Ss before fixing y. -/
theorem transfer_error_from_scale (rows n M W N T k : ℕ) (α eps Ss Z : ℝ)
    (hα : 0<α) (heps : 0≤eps) (hZ : 0≤Z)
    (hscale : (rows:ℝ)≤α^k*(W:ℝ)^2*Z)
    (hbox : (W:ℝ)^2*((n:ℝ)*(M:ℝ))≤(N:ℝ)*(T:ℝ))
    (hchoose : Z*(k:ℝ)*eps≤Ss/200) :
    (rows:ℝ)*((k:ℝ)*(eps*(n:ℝ)*(M:ℝ)))≤α^k*(Ss*((N:ℝ)*(T:ℝ)))/200 := by
  calc
    _≤(α^k*(W:ℝ)^2*Z)*((k:ℝ)*(eps*(n:ℝ)*(M:ℝ))) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _=(α^k*Z*(k:ℝ)*eps)*((W:ℝ)^2*((n:ℝ)*(M:ℝ))) := by ring
    _≤(α^k*Z*(k:ℝ)*eps)*((N:ℝ)*(T:ℝ)) :=
      mul_le_mul_of_nonneg_left hbox (by positivity)
    _=(α^k*((N:ℝ)*(T:ℝ)))*(Z*(k:ℝ)*eps) := by ring
    _≤(α^k*((N:ℝ)*(T:ℝ)))*(Ss/200) :=
      mul_le_mul_of_nonneg_left hchoose (by positivity)
    _=_ := by ring

end ActualRayConditionalLower318
