module
public import ActualTZOrdinaryLeadingDecay318
public import ActualTZOrdinaryFineRemainder318
public import ActualTZCollisionLogEnvelope318
import all ActualTZCollisionPrimePartition318
public section
noncomputable section
namespace ActualTZOrdinaryCollisionCutoffRate318
open Filter
open scoped BigOperators Topology
open ActualTZOrdinaryNumericDensity318 ActualTZOrdinaryLeadingDecay318
open ActualTZOrdinaryFineRemainder318 ActualTZCollisionLogEnvelope318
open ActualTZPhysicalCorrectionBound318 ActualTZPhysicalEulerSplit318
open ActualTZCollisionPrimePartition318 ActualTZWeightedPrimePrefix318

/-- The averaged collision part has exactly the fixed-y limsup
form; the log-modulus factor and sqrt N constant are separated.
This bound is uniform in the independent analytic Euler truncation. -/
theorem fixed_cutoff (k : ℕ) (A C : ℝ) (hC : 0≤C) :
    ∃ y₀ : ℕ,1<y₀ ∧ ∀ y≥y₀,∀ ε>0,∀ d>0,∃ N₀ : ℕ,∀ N≥N₀,
      ∀ (W P K : ℕ),0<K→(∀ p,p.Prime→p≤y→p∣W)→Real.log K≤A*(y:ℝ)→
      ∀ M : ℝ,d*(N:ℝ)^((1:ℝ)/2)≤M→
      let G := goodConst k*(∑ p∈offWheel W P,(1/(p:ℝ))^2)+badConst k*extra W P K
      (Real.exp G-1)+Real.exp G*(∑ p∈regular y N K,
        prefixWeight (badConst k) p*(C*(1/(p:ℝ)+1/M)))≤leading k A C y+ε := by
  obtain ⟨Y,hY⟩ := eventually_quarter (badConst k*Real.exp 1)
    (mul_nonneg (bad_nonnegative k) (Real.exp_pos _).le)
  obtain ⟨y₀,hy₀⟩ := exists_nat_gt (max (1:ℝ) Y)
  have hOne : 1<y₀ := by exact_mod_cast ((le_max_left (1:ℝ) Y).trans_lt hy₀)
  refine ⟨y₀,hOne,?_⟩
  intro y hy ε hε d hd
  let Q := Real.exp (Gbound k A y)*multiplier k C
  have hQ : 0≤Q := by
    unfold Q multiplier
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg (bad_nonnegative k) hC))
  have hGoal : 0<ε/(1+Q) := by positivity
  have hFine := (fine_tendsto d).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ=>(n:ℝ)) atTop atTop)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hFine.eventually (gt_mem_nhds hGoal))
  refine ⟨max 1 N₀,?_⟩
  intro N hN W P K hK hWheel hA M hM G
  have hN₀' : N₀≤N := (le_max_right _ _).trans hN
  have hNOne : 1≤N := (le_max_left _ _).trans hN
  have hNpos : 0<N := by omega
  have hNreal : (0:ℝ)<N := by exact_mod_cast hNpos
  have hMpos := (mul_pos hd (Real.rpow_pos_of_pos hNreal ((1:ℝ)/2))).trans_le hM
  have hy' : 1<y := hOne.trans_le hy
  have hPrime (p : ℕ) (hh : y<p) :
      (1+Real.log p)^(badConst k*Real.exp 1)≤(p:ℝ)^((1:ℝ)/4) := by
    apply hY
    exact ((le_max_right (1:ℝ) Y).trans hy₀.le).trans
      (by exact_mod_cast (hy.trans hh.le))
  have H := numeric_bound W P y N K k hy' hNpos hK hWheel A C M hC hMpos hA hPrime
  apply H.trans
  have hF := pointwise N hNpos d M hd hM
  have hF' := hF.trans_lt (hN₀ N hN₀')
  have hE : Q*Fbound N M≤ε := by
    have hB := (lt_div_iff₀ (show 0<1+Q by positivity)).1 hF'
    have hF0 : 0≤Fbound N M := by
      unfold Fbound
      have hu : (1:ℝ)≤(2*N+1:ℕ) := by exact_mod_cast (show 1≤2*N+1 by omega)
      have hp : 1≤1+Real.log (2*N+1:ℕ) := le_add_of_nonneg_right (Real.log_nonneg hu)
      exact div_nonneg (mul_nonneg (by positivity)
        (mul_nonneg (Real.exp_pos _).le (Real.log_nonneg hp))) hMpos.le
    nlinarith only [hB,hF0]
  exact add_le_add_left hE _

end ActualTZOrdinaryCollisionCutoffRate318
