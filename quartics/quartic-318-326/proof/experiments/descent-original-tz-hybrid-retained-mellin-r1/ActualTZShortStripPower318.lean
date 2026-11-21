module
public import Mathlib
public section
noncomputable section
namespace ActualTZShortStripPower318
open Filter Asymptotics
open scoped Topology

/-- Actual ReadyWindow exponent 8kρ<1 simultaneously absorbs
the original short n^-1/4 mass and the smaller exact-zero mass,
after the old divisor cutoff bound and fixed-y scale. -/
theorem strict_decay (k : ℕ) (ρ : ℝ) (h : 8*(k:ℝ)*ρ<1) :
    Tendsto (fun x : ℝ=>Real.log x^k*x^(2*(k:ℝ)*ρ-(1:ℝ)/4)) atTop (𝓝 0) := by
  have hp : 0<(1:ℝ)/4-2*(k:ℝ)*ρ := by linarith
  have H := (_root_.isLittleO_log_rpow_rpow_atTop (k:ℝ) hp).tendsto_div_nhds_zero
  refine H.congr' ?_
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  rw [Real.rpow_natCast,div_eq_mul_inv,show 2*(k:ℝ)*ρ-(1:ℝ)/4= -((1:ℝ)/4-2*(k:ℝ)*ρ) by ring,
    Real.rpow_neg (zero_le_one.trans hx)]

theorem literal_bound_decay (k : ℕ) (ρ C : ℝ) (h : 8*(k:ℝ)*ρ<1) :
    Tendsto (fun x : ℝ=>
      (Real.log (x^ρ)*(2*x^ρ*C)^2)^k*x^(-(1:ℝ)/4)) atTop (𝓝 0) := by
  let A : ℝ := (ρ*(2*C)^2)^k
  have H := (tendsto_const_nhds : Tendsto (fun _ : ℝ=>A) atTop (𝓝 A)).mul
    (strict_decay k ρ h)
  rw [mul_zero] at H
  refine H.congr' ?_
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hxp : 0<x := zero_lt_one.trans_le hx
  have hex : ((x^ρ)^(2*k:ℕ))=x^(2*(k:ℝ)*ρ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hxp.le]
    push_cast
    congr 1 <;> ring
  have hBase : Real.log (x^ρ)*(2*x^ρ*C)^2 =
      (ρ*(2*C)^2)*Real.log x*(x^ρ)^2 := by
    rw [Real.log_rpow hxp]
    ring
  change A*(Real.log x^k*x^(2*(k:ℝ)*ρ-(1:ℝ)/4))=
    (Real.log (x^ρ)*(2*x^ρ*C)^2)^k*x^(-(1:ℝ)/4)
  rw [hBase,mul_pow,mul_pow,←pow_mul,hex]
  rw [show (2*(k:ℝ)*ρ-(1:ℝ)/4)=2*(k:ℝ)*ρ+(-(1:ℝ)/4) by ring,
    Real.rpow_add hxp]
  dsimp only [A]
  ring

end ActualTZShortStripPower318
