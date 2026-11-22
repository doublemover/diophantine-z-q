module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

public section
noncomputable section

open Filter
open scoped Topology

namespace SelectedActualEllipticAnalyticRotation318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem analytic_power_normal_form {f : ℂ → ℂ} {c : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f c) (hn : 0 < n)
    (ho : analyticOrderAt f c = n) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k c ∧ k c = 0 ∧ deriv k c ≠ 0 ∧
      (∀ᶠ w in 𝓝 c, f w = (k w)^n) := by
  obtain ⟨u,hu,huc,hfac⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  obtain ⟨r,hr⟩ := IsAlgClosed.exists_pow_nat_eq (u c) hn
  have hrn : r ≠ 0 := by
    intro h
    rw [h,zero_pow (Nat.ne_of_gt hn)] at hr
    exact huc hr.symm
  let P : ℂ → ℂ := fun w => w^n
  have hP : AnalyticAt ℂ P r := analyticAt_id.fun_pow n
  have hPd : deriv P r ≠ 0 := by
    have hd : HasDerivAt P ((n : ℂ)*r^(n-1)*1) r := (hasDerivAt_id' r).fun_pow n
    rw [hd.deriv]
    exact mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
      (pow_ne_zero _ hrn)) one_ne_zero
  let R := hP.hasStrictDerivAt.localInverse P (deriv P r) r hPd
  have hRa : AnalyticAt ℂ R (P r) := hP.analyticAt_localInverse hPd
  have hRl : ∀ᶠ w in 𝓝 r, R (P w) = w :=
    hP.hasStrictDerivAt.eventually_left_inverse hPd
  have hRr : ∀ᶠ y in 𝓝 (P r), P (R y) = y :=
    hP.hasStrictDerivAt.eventually_right_inverse hPd
  have hRc : R (u c) = r := by
    rw [← hr]
    exact hRl.self_of_nhds
  have hRac : AnalyticAt ℂ R (u c) := by
    rw [← hr]
    exact hRa
  let v := R ∘ u
  have hv : AnalyticAt ℂ v c := hRac.comp hu
  have hvc : v c = r := hRc
  have hRv : ∀ᶠ z in 𝓝 c, (v z)^n = u z := by
    have ht : Tendsto u (𝓝 c) (𝓝 (P r)) := by
      have hr' : P r = u c := hr
      rw [hr']
      exact hu.continuousAt.tendsto
    exact ht.eventually hRr
  let k := fun z : ℂ => (z-c)*v z
  have hk : AnalyticAt ℂ k c :=
    (analyticAt_id.fun_sub analyticAt_const).fun_mul hv
  have hkc : k c = 0 := by simp only [k,sub_self,zero_mul]
  have hkd : deriv k c ≠ 0 := by
    have ha : HasDerivAt (fun z : ℂ => z-c) 1 c := (hasDerivAt_id' c).sub_const c
    have hd : HasDerivAt k (1 * v c + (c-c) * deriv v c) c := ha.fun_mul hv.differentiableAt.hasDerivAt
    rw [hd.deriv,one_mul,sub_self,zero_mul,add_zero,hvc]
    exact hrn
  refine ⟨k,hk,hkc,hkd,?_⟩
  filter_upwards [hfac,hRv] with w hfw hvw
  change f w = ((w-c)*v w)^n
  rw [hfw,mul_pow,hvw,smul_eq_mul]

/-- A holomorphic germ of finite order greater than one has a genuinely
nontrivial analytic symmetry fixing the same center, preserving the germ,
and moving every point near enough on the puncture. Both target and
source neighborhoods are the original complex plane near c. -/
theorem analytic_rotation_of_order_gt_one {f : ℂ → ℂ} {c : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f c) (hn : 1 < n)
    (ho : analyticOrderAt f c = n) :
    ∃ σ : ℂ → ℂ, AnalyticAt ℂ σ c ∧ σ c = c ∧
      (f ∘ σ) =ᶠ[𝓝 c] f ∧
      (∀ᶠ w in 𝓝[≠] c, σ w ≠ c ∧ σ w ≠ w) := by
  obtain ⟨k,hk,hkc,hkd,hfPow⟩ := analytic_power_normal_form hf (by omega) ho
  let S := hk.hasStrictDerivAt.localInverse k (deriv k c) c hkd
  have hSa : AnalyticAt ℂ S 0 := by
    rw [← hkc]
    exact hk.analyticAt_localInverse hkd
  have hSl : ∀ᶠ w in 𝓝 c, S (k w) = w :=
    hk.hasStrictDerivAt.eventually_left_inverse hkd
  have hSr : ∀ᶠ y in 𝓝 (0 : ℂ), k (S y) = y := by
    rw [← hkc]
    exact hk.hasStrictDerivAt.eventually_right_inverse hkd
  have hSc : S 0 = c := by
    rw [← hkc]
    exact hSl.self_of_nhds
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (by omega)
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  let H := fun w => ζ * k w
  have hH : AnalyticAt ℂ H c := analyticAt_const.fun_mul hk
  have hHc : H c = 0 := by
    change ζ * k c = 0
    rw [hkc,mul_zero]
  have htH : Tendsto H (𝓝 c) (𝓝 (0 : ℂ)) := by
    rw [← hHc]
    exact hH.continuousAt.tendsto
  let σ := S ∘ H
  have hσ : AnalyticAt ℂ σ c := (show AnalyticAt ℂ S (H c) from hHc.symm ▸ hSa).comp hH
  have hσc : σ c = c := by change S (H c) = c; rw [hHc,hSc]
  have htσ : Tendsto σ (𝓝 c) (𝓝 c) := by
    have hRaw : Tendsto σ (𝓝 c) (𝓝 (σ c)) := hσ.continuousAt.tendsto
    simpa only [hσc] using hRaw
  have hkσ : ∀ᶠ w in 𝓝 c, k (σ w) = ζ * k w := htH.eventually hSr
  refine ⟨σ,hσ,hσc,?_,?_⟩
  · filter_upwards [htσ.eventually hfPow,hfPow,hkσ] with w hu hw hs
    change f (σ w) = f w
    rw [hu,hw,hs,mul_pow,hζ.pow_eq_one,one_mul]
  · filter_upwards [hSl.filter_mono nhdsWithin_le_nhds,
      hkσ.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hs hp
    have hwc : w ≠ c := fun h => hp (Set.mem_singleton_iff.mpr h)
    have hkw : k w ≠ 0 := by
      intro hz
      rw [hz,hSc] at hw
      exact hwc hw.symm
    refine ⟨?_,?_⟩
    · intro h
      rw [h,hkc] at hs
      exact (mul_ne_zero hζ0 hkw) hs.symm
    · intro h
      rw [h] at hs
      have hh : 1 * k w = ζ * k w := (one_mul _).trans hs
      exact hζ.ne_one hn (mul_right_cancel₀ hkw hh).symm

end SelectedActualEllipticAnalyticRotation318

#print axioms SelectedActualEllipticAnalyticRotation318.analytic_rotation_of_order_gt_one
