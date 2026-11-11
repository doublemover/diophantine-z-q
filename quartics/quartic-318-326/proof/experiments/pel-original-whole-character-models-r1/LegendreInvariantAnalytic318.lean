module
public import LegendreInvariantTangent318
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public section
noncomputable section
namespace LegendreInvariantAnalytic318
open Set Filter
open scoped Topology
open LegendreIndependentGraphs318 LegendreInvariantTangent318
open NormalizedLegendreProjectiveModel318

/-- Differentiate the SAME finite plane equation along an actual analytic
parameter, rather than assuming its tangent constraint. -/
lemma finite_derivative (l : ℂ) (x y : ℂ→ℂ) {z : ℂ}
    (hx : DifferentiableAt ℂ x z) (hy : DifferentiableAt ℂ y z)
    (he : ∀ᶠ w in 𝓝 z,finiteEquation l (x w,y w)=0) :
    finiteSlope l (x z)*deriv x z=2*y z*deriv y z := by
  have hd:=(((hy.hasDerivAt.pow 2).sub (hx.hasDerivAt.pow 3)).sub
    (hx.hasDerivAt.const_mul (A l))).sub_const (B l)
  have hc : HasDerivAt (fun _ : ℂ=>0)
      (2*y z*deriv y z-3*(x z)^2*deriv x z-A l*deriv x z) z := by
    convert hd.congr_of_eventuallyEq (he.symm) using 1 <;> simp [finiteEquation] <;> ring
  have hz:=hc.unique (hasDerivAt_const z (0:ℂ))
  dsimp [finiteSlope]
  linear_combination -hz

lemma infinity_derivative (l : ℂ) (u v : ℂ→ℂ) {z : ℂ}
    (hu : DifferentiableAt ℂ u z) (hv : DifferentiableAt ℂ v z)
    (he : ∀ᶠ w in 𝓝 z,infinityEquation l (u w,v w)=0) :
    J l (u z) (v z)*deriv v z=H l (u z) (v z)*deriv u z := by
  have hd:=((hv.hasDerivAt.sub (hu.hasDerivAt.pow 3)).sub
    ((hu.hasDerivAt.const_mul (A l)).mul (hv.hasDerivAt.pow 2))).sub
      ((hv.hasDerivAt.pow 3).const_mul (B l))
  have hc : HasDerivAt (fun _ : ℂ=>0)
      (J l (u z) (v z)*deriv v z-H l (u z) (v z)*deriv u z) z := by
    convert hd.congr_of_eventuallyEq (he.symm) using 1 <;> simp [infinityEquation,J,H] <;> ring
  exact sub_eq_zero.mp (hc.unique (hasDerivAt_const z (0:ℂ)))

@[expose] def finiteCoefficient (l : ℂ) (x y : ℂ→ℂ) (z : ℂ) : ℂ :=
  finiteValue l (x z) (y z) (deriv x z) (deriv y z)
@[expose] def infinityCoefficient (l : ℂ) (u v : ℂ→ℂ) (z : ℂ) : ℂ :=
  infinityValue l (u z) (v z) (deriv u z) (deriv v z)

variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]
/-- Holomorphy across the finite branch locus follows from the alternate
actual dy/P'(t) formula. Piecewise evaluation is not mistaken for continuity. -/
theorem finite_analytic (x y : ℂ→ℂ) (s : Set ℂ) (hs : IsOpen s)
    (hx : AnalyticOnNhd ℂ x s) (hy : AnalyticOnNhd ℂ y s)
    (he : ∀ z∈s,finiteEquation l (x z,y z)=0) :
    AnalyticOnNhd ℂ (finiteCoefficient l x y) s := by
  intro z hz
  have hxz:=hx z hz
  have hyz:=hy z hz
  by_cases hY : 2*y z≠0
  · have hden : AnalyticAt ℂ (fun w=>2*y w) z := analyticAt_const.mul (hy z hz)
    have hn:=hden.continuousAt.eventually_ne hY
    apply ((hx z hz).deriv.div hden hY).congr
    filter_upwards [hn] with w hw
    exact (finite_x_formula l (x w) (y w) (deriv x w) (deriv y w) hw).symm
  · have hX : finiteSlope l (x z)≠0 := by
      rcases finite_partial_nonzero l (x z,y z) (he z hz) with h|h
      · exact (hY h).elim
      · exact neg_ne_zero.mp h
    have hden : AnalyticAt ℂ (fun w=>finiteSlope l (x w)) z := by
      dsimp [finiteSlope]
      fun_prop
    have hn:=hden.continuousAt.eventually_ne hX
    apply ((hy z hz).deriv.div hden hX).congr
    filter_upwards [hn,hs.mem_nhds hz] with w hw hws
    have ht:=finite_derivative l x y (hx w hws).differentiableAt (hy w hws).differentiableAt
      (Filter.eventually_of_mem (hs.mem_nhds hws) (fun a ha=>he a ha))
    exact (finite_y_formula l (x w) (y w) (deriv x w) (deriv y w) hw ht).symm

/-- The independent infinity atlas uses either true implicit coordinate;
the two expressions agree on overlaps and are holomorphic through U=V=0. -/
theorem infinity_analytic (u v : ℂ→ℂ) (s : Set ℂ) (hs : IsOpen s)
    (hu : AnalyticOnNhd ℂ u s) (hv : AnalyticOnNhd ℂ v s)
    (he : ∀ z∈s,infinityEquation l (u z,v z)=0) :
    AnalyticOnNhd ℂ (infinityCoefficient l u v) s := by
  intro z hz
  have huz:=hu z hz
  have hvz:=hv z hz
  by_cases hj : J l (u z) (v z)≠0
  · have hden : AnalyticAt ℂ (fun w=>J l (u w) (v w)) z := by
      dsimp [J]
      fun_prop
    have hn:=hden.continuousAt.eventually_ne hj
    apply ((hu z hz).deriv.neg.div hden hj).congr
    filter_upwards [hn] with w hw
    exact (infinity_u_formula l (u w) (v w) (deriv u w) (deriv v w) hw).symm
  · have hh : H l (u z) (v z)≠0 := by
      rcases LegendreInfinityIndependentGraphs318.partial_nonzero l (u z,v z) (he z hz) with h|h
      · exact (hj h).elim
      · exact neg_ne_zero.mp h
    have hden : AnalyticAt ℂ (fun w=>H l (u w) (v w)) z := by
      dsimp [H]
      fun_prop
    have hn:=hden.continuousAt.eventually_ne hh
    apply ((hv z hz).deriv.neg.div hden hh).congr
    filter_upwards [hn,hs.mem_nhds hz] with w hw hws
    have ht:=infinity_derivative l u v (hu w hws).differentiableAt (hv w hws).differentiableAt
      (Filter.eventually_of_mem (hs.mem_nhds hws) (fun a ha=>he a ha))
    exact (infinity_v_formula l (u w) (v w) (deriv u w) (deriv v w) hw ht).symm
end LegendreInvariantAnalytic318
