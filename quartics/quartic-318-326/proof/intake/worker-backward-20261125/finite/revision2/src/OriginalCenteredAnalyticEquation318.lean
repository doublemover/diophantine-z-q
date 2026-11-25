module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Tactic.Ring

/-!
  Centered analytic chart: the normalised tuple of actual equations is
  y - residual x y, with invertible y-linear term. The proof constructs
  a branch from the zero-start Picard limit, without a supplied solution
  or separate analytic point. In ℂ^m the assumptions are uniform bounds
  for the degree-at-least-two polynomial residual on the chosen polydisc.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace OriginalCenteredAnalyticEquation318

variable {W : Type*} [NormedAddCommGroup W]

private def step (F : W → W) : ℕ → W
  | 0 => 0
  | n+1 => F (step F n)

private theorem fixed [CompleteSpace W] (F : W → W) {ρ q : ℝ}
    (hρ : 0 < ρ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hzero : ‖F 0‖ ≤ (1-q) * ρ)
    (hlip : ∀ u v, ‖u‖ ≤ ρ → ‖v‖ ≤ ρ → ‖F u - F v‖ ≤ q * ‖u-v‖) :
    ∃ u, ‖u‖ ≤ ρ ∧ F u = u := by
  have hmaps : ∀ u, ‖u‖ ≤ ρ → ‖F u‖ ≤ ρ := by
    intro u hu
    calc
      ‖F u‖ = ‖(F u - F 0) + F 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖F u - F 0‖ + ‖F 0‖ := norm_add_le _ _
      _ ≤ q * ρ + (1-q) * ρ := by
        have hz : ‖(0 : W)‖ ≤ ρ := by simpa only [norm_zero] using hρ.le
        have hF : ‖F u - F 0‖ ≤ q*‖u‖ := by
          simpa only [sub_zero] using hlip u 0 hu hz
        exact add_le_add (hF.trans (mul_le_mul_of_nonneg_left hu hq0)) hzero
      _ = ρ := by ring
  have hb : ∀ n, ‖step F n‖ ≤ ρ := by
    intro n
    induction n with
    | zero => simpa only [step, norm_zero] using hρ.le
    | succ n ih => exact hmaps _ ih
  have hd : ∀ n, ‖step F n - step F (n+1)‖ ≤ ρ * q^n := by
    intro n
    induction n with
    | zero =>
      simpa only [step, zero_sub, norm_neg, pow_zero, mul_one] using
        (hmaps 0 (by simpa only [norm_zero] using hρ.le))
    | succ n ih =>
      calc
        ‖step F (n+1) - step F (n+1+1)‖ ≤
            q * ‖step F n - step F (n+1)‖ := hlip _ _ (hb n) (hb (n+1))
        _ ≤ q * (ρ * q^n) := mul_le_mul_of_nonneg_left ih hq0
        _ = ρ * q^(n+1) := by rw [pow_succ]; ac_rfl
  have hc : CauchySeq (step F) :=
    cauchySeq_of_le_geometric q ρ hq1 (by simpa only [dist_eq_norm] using hd)
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hc
  have hub : ‖u‖ ≤ ρ := le_of_tendsto' (continuous_norm.continuousAt.tendsto.comp hu) hb
  have hsucc : Tendsto (fun n => step F (n+1)) atTop (𝓝 u) :=
    (tendsto_add_atTop_iff_nat (f := step F) 1).2 hu
  have hnorm : Tendsto (fun n => ‖step F (n+1) - F u‖) atTop
      (𝓝 ‖u - F u‖) := by
    simpa only [dist_eq_norm] using hsucc.dist
      (show Tendsto (fun _ : ℕ => F u) atTop (𝓝 (F u)) from tendsto_const_nhds)
  have hsmall : Tendsto (fun n => q * ‖step F n-u‖) atTop (𝓝 0) := by
    have hus : Tendsto (fun n => ‖step F n-u‖) atTop (𝓝 ‖u-u‖) := by
      simpa only [dist_eq_norm] using hu.dist
        (show Tendsto (fun _ : ℕ => u) atTop (𝓝 u) from tendsto_const_nhds)
    have hq' : Tendsto (fun _ : ℕ => q) atTop (𝓝 q) := tendsto_const_nhds
    have hm := hq'.mul hus
    simpa only [sub_self, norm_zero, mul_zero] using hm
  have hle : ‖u - F u‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' hnorm hsmall fun n => hlip _ _ (hb n) hub
  have hf : u - F u = 0 := norm_eq_zero.1 (le_antisymm hle (norm_nonneg _))
  exact ⟨u, hub, (sub_eq_zero.1 hf).symm⟩

private theorem fixed_unique (F : W → W) {ρ q : ℝ} (hq : q < 1)
    (hlip : ∀ u v, ‖u‖ ≤ ρ → ‖v‖ ≤ ρ → ‖F u-F v‖ ≤ q*‖u-v‖)
    {u v : W} (hu : ‖u‖ ≤ ρ) (hv : ‖v‖ ≤ ρ)
    (eu : F u = u) (ev : F v = v) : u = v := by
  have hh := hlip u v hu hv
  rw [eu, ev] at hh
  have hz : (1-q) * ‖u-v‖ ≤ 0 := by
    rw [sub_mul, one_mul]
    exact sub_nonpos.mpr hh
  have hn : ‖u-v‖ ≤ 0 := nonpos_of_mul_nonpos_right hz (sub_pos.2 hq)
  exact sub_eq_zero.1 <| norm_eq_zero.1 <| le_antisymm hn (norm_nonneg _)

variable {V : Type*} [NormedAddCommGroup V]

/-- Solve the given equations on every parameter of the same closed polydisc.
The tuple returned is a literal zero of y - R(x,y); every zero of the same
equations in the selected polydisc is this tuple. No branch choice is an input. -/
theorem zeroChart [CompleteSpace W] (R : V → W → W) {r ρ q : ℝ}
    (hρ : 0 < ρ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hR0 : ∀ x, ‖x‖ ≤ r → ‖R x 0‖ ≤ (1-q)*ρ)
    (hRy : ∀ x, ‖x‖ ≤ r → ∀ u v, ‖u‖ ≤ ρ → ‖v‖ ≤ ρ →
      ‖R x u - R x v‖ ≤ q*‖u-v‖) :
    ∃ y : V → W,
      (∀ x, ‖x‖ ≤ r → ‖y x‖ ≤ ρ ∧ y x - R x (y x) = 0) ∧
      (∀ x v, ‖x‖ ≤ r → ‖v‖ ≤ ρ → (v-R x v = 0 ↔ v = y x)) := by
  classical
  have h : ∀ x, ‖x‖ ≤ r → ∃ v, ‖v‖ ≤ ρ ∧ R x v = v := by
    intro x hx
    exact fixed (R x) hρ hq0 hq1 (hR0 x hx) (hRy x hx)
  let y : V → W := fun x => if hx : ‖x‖ ≤ r then Classical.choose (h x hx) else 0
  have hy : ∀ x, ‖x‖ ≤ r → ‖y x‖ ≤ ρ ∧ R x (y x) = y x := by
    intro x hx
    simpa only [y, dite_eq_left hx] using Classical.choose_spec (h x hx)
  refine ⟨y, ?_, ?_⟩
  · intro x hx
    exact ⟨(hy x hx).1, sub_eq_zero.2 (hy x hx).2.symm⟩
  · intro x v hx hv
    constructor
    · intro he
      exact fixed_unique (R x) hq1 (hRy x hx) hv (hy x hx).1
        (sub_eq_zero.1 he).symm (hy x hx).2
    · intro he
      rw [he]
      exact sub_eq_zero.2 (hy x hx).2.symm

/-- The returned branch has a uniform second-order bound at the actual
marked origin. A chart normalised by Y'=Y+J⁻¹LX therefore has precisely
the original marked first-order tangent Y=-J⁻¹LX, with no new scale. -/
theorem zeroChart_linear_read (R : V → W → W) (x : V) (y : W) {K q : ℝ}
    (hq : q < 1) (hy : y-R x y = 0)
    (h0 : ‖R x 0‖ ≤ K*‖x‖^2)
    (hLip : ‖R x y - R x 0‖ ≤ q*‖y‖) :
    ‖y‖ ≤ K*‖x‖^2/(1-q) := by
  apply (le_div_iff₀ (sub_pos.2 hq)).2
  have hsum : ‖y‖ ≤ q*‖y‖+K*‖x‖^2 := by
    calc
      ‖y‖ = ‖(R x y - R x 0)+R x 0‖ := by
        rw [sub_add_cancel, ← sub_eq_zero.1 hy]
      _ ≤ ‖R x y-R x 0‖+‖R x 0‖ := norm_add_le _ _
      _ ≤ q*‖y‖+K*‖x‖^2 := add_le_add hLip h0
  rw [mul_sub, mul_one, mul_comm ‖y‖ q]
  exact sub_le_iff_le_add.2 (by simpa only [add_comm] using hsum)

/-- The same exact zeros are Lipschitz in the free-coordinate parameter.
This establishes genuine analytic-chart continuity, rather than just
pointwise solvability, as soon as the actual polynomials give hMotion. -/
theorem zeroChart_parameter (R : V → W → W) (x x' : V) (y y' : W) {L q : ℝ}
    (hq : q < 1) (hy : y-R x y = 0) (hy' : y'-R x' y' = 0)
    (hMove : ‖R x y - R x' y‖ ≤ L*‖x-x'‖)
    (hLip : ‖R x' y - R x' y'‖ ≤ q*‖y-y'‖) :
    ‖y-y'‖ ≤ L*‖x-x'‖/(1-q) := by
  apply (le_div_iff₀ (sub_pos.2 hq)).2
  have hsum : ‖y-y'‖ ≤ L*‖x-x'‖+q*‖y-y'‖ := by
    calc
      ‖y-y'‖ = ‖(R x y-R x' y)+(R x' y-R x' y')‖ := by
        rw [sub_add_sub_cancel, ← sub_eq_zero.1 hy, ← sub_eq_zero.1 hy']
      _ ≤ ‖R x y-R x' y‖+‖R x' y-R x' y'‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hMove hLip
  rw [mul_sub, mul_one, mul_comm ‖y-y'‖ q]
  exact sub_le_iff_le_add.2 hsum

end OriginalCenteredAnalyticEquation318
