module
public import RealQuarticSumU318
public import RealQuarticOvalCover318
public import Mathlib.Analysis.Analytic.Uniqueness
public section
noncomputable section
namespace RealQuarticSumAnalytic318
open Set Filter ReciprocalGroup318 RealQuarticSumU318
open scoped Topology
set_option maxHeartbeats 2000000
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma sumU_analytic {D : ℝ} (hD : 0<D) {u v a b : V → ℝ} {x : V}
    (hu : AnalyticAt ℝ u x) (hv : AnalyticAt ℝ v x)
    (ha : AnalyticAt ℝ a x) (hb : AnalyticAt ℝ b x) :
    AnalyticAt ℝ (fun t => sumU D (u t) (v t) (a t) (b t)) x := by
  exact ((hu.mul hb).add (ha.mul hv)).div
    (analyticAt_const.add ((analyticAt_const.mul (hu.pow 2)).mul (ha.pow 2)))
    (denominator_ne hD _ _)

lemma sumV_analytic {D : ℝ} (hD : 0<D) {u v a b : V → ℝ} {x : V}
    (hu : AnalyticAt ℝ u x) (hv : AnalyticAt ℝ v x)
    (ha : AnalyticAt ℝ a x) (hb : AnalyticAt ℝ b x) :
    AnalyticAt ℝ (fun t => sumV D (u t) (v t) (a t) (b t)) x := by
  exact (((hv.mul hb).mul
    (analyticAt_const.sub ((analyticAt_const.mul (hu.pow 2)).mul (ha.pow 2)))).sub
    ((((analyticAt_const.mul analyticAt_const).mul hu).mul ha).mul
      ((hu.pow 2).add (ha.pow 2)))).div
    ((analyticAt_const.add ((analyticAt_const.mul (hu.pow 2)).mul (ha.pow 2))).pow 2)
    (pow_ne_zero _ (denominator_ne hD _ _))

/-- Analytic square roots with the same nonzero reference value agree
throughout the connected covering space. There is no pointwise sign choice. -/
lemma analytic_square_identity {f g : V → ℝ}
    (hf : AnalyticOnNhd ℝ f univ) (hg : AnalyticOnNhd ℝ g univ)
    (hsq : ∀ x, (f x)^2=(g x)^2) (h0 : f 0=g 0) (hn : f 0≠0) : f=g := by
  have hs : f 0+g 0≠0 := by rw [←h0]; intro hz; apply hn; linarith
  have hev : ∀ᶠ x in 𝓝 (0:V), f x+g x≠0 :=
    ((hf 0 (mem_univ 0)).continuousAt.add (hg 0 (mem_univ 0)).continuousAt).eventually_ne hs
  apply hf.eq_of_eventuallyEq hg
  filter_upwards [hev] with x hx
  have hp : (f x-g x)*(f x+g x)=0 := by nlinarith [hsq x]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hx)

end RealQuarticSumAnalytic318
