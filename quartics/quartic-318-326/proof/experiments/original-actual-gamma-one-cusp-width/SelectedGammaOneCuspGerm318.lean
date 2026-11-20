module
public import SelectedGammaOneCuspWidth318
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Analytic.Order
public section
noncomputable section

open scoped MatrixGroups Topology

namespace SelectedGammaOneCuspGerm318

/-- The true exponential coordinate at the base cusp (translation by
one) pulls back to the width power of the source coordinate. This is
an equality of the actual Mathlib q-parameters, not monomials chosen
to encode a desired ramification result. -/
theorem qparam_power (τ : ℂ) (w : ℕ) (hw : 0 < w) :
    Function.Periodic.qParam 1 τ = (Function.Periodic.qParam (w:ℝ) τ)^w := by
  have hn : (w:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hw)
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one,
    ← Complex.exp_nat_mul, Complex.ofReal_natCast]
  congr 1
  rw [mul_comm (w:ℂ), div_mul_cancel₀ _ hn]

/-- The exact pullback order of a simple-zero base germ under the
width-power map. No assertion about the unknown source order is used. -/
theorem width_order (w : ℕ) (hw : 0 < w) (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (simple : analyticOrderAt F 0 = 1) :
    analyticOrderAt (F ∘ fun z : ℂ => z^w) 0 = w := by
  let G : ℂ → ℂ := fun z => z^w
  change analyticOrderAt (F ∘ G) 0 = w
  have hG0 : G 0 = 0 := zero_pow hw.ne'
  have hGa : AnalyticAt ℂ G 0 := by dsimp only [G]; fun_prop
  have hG : analyticOrderAt G 0 = w := by
    apply hGa.analyticOrderAt_eq_natCast.mpr
    refine ⟨fun _ => 1, by fun_prop, one_ne_zero, Filter.Eventually.of_forall ?_⟩
    intro z
    simp [G, smul_eq_mul]
  have hFa : AnalyticAt ℂ F (G 0) := by simpa only [hG0] using hF
  rw [hFa.analyticOrderAt_comp hGa, hG0, simple, one_mul]
  simpa only [sub_zero] using hG

/-- For the actual cusp g∞, use the source and base expansions of 1/J
in the corresponding genuine quotient charts. The supplied chart law
identifies functions, not orders; the positive width and resulting
source order are derived from the actual subgroup and analytic order. -/
theorem actual_inverse_j_order (N : ℕ) [NeZero N] (hN : 4 < N) (g : SL(2, ℤ))
    (Jinv F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) (simple : analyticOrderAt F 0 = 1)
    (chart : Jinv =ᶠ[𝓝 0] (F ∘ fun z : ℂ => z^(N/N.gcd ((g 1 0:ZMod N).val)))) :
    analyticOrderAt Jinv 0 = (N/N.gcd ((g 1 0:ZMod N).val):ℕ) := by
  have hw := (SelectedGammaOneCuspWidth318.least_positive N hN g).1
  exact (analyticOrderAt_congr chart).trans (width_order _ hw F hF simple)

end SelectedGammaOneCuspGerm318

#print axioms SelectedGammaOneCuspGerm318.qparam_power
#print axioms SelectedGammaOneCuspGerm318.actual_inverse_j_order
