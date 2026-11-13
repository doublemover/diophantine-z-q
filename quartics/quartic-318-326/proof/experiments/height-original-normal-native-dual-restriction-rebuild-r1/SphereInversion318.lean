module
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Complex.Basic
public section
noncomputable section
open Function Filter Topology
open scoped OnePoint
namespace SphereInversion318
set_option maxHeartbeats 0

/-- Independent inversion of the standard complex sphere, exchanging zero
and infinity. No modular source or transported topology appears here. -/
@[expose] def inversion (z : OnePoint ℂ) : OnePoint ℂ :=
  z.elim (0:ℂ) (fun t => if t=0 then ∞ else (t⁻¹:ℂ))

lemma inversion_infty : inversion ∞ = (0:ℂ) := rfl
lemma inversion_zero : inversion (0:ℂ) = ∞ := by simp [inversion]
lemma inversion_coe {t : ℂ} (ht : t ≠ 0) : inversion (t : OnePoint ℂ) = (t⁻¹:ℂ) := by
  simp [inversion,ht]

theorem inversion_involutive : Involutive inversion := by
  intro z
  induction z using OnePoint.rec with
  | infty => rw [inversion_infty,inversion_zero]
  | coe t =>
    by_cases ht : t=0
    · subst t; rw [inversion_zero,inversion_infty]
    · rw [inversion_coe ht,inversion_coe (inv_ne_zero ht),inv_inv]

lemma coe_inversion_continuousAt (t : ℂ) :
    ContinuousAt (fun x : ℂ => inversion (x : OnePoint ℂ)) t := by
  by_cases ht : t=0
  · subst t
    rw [continuousAt_iff_punctured_nhds,inversion_zero]
    have hc : Tendsto ((↑) : ℂ → OnePoint ℂ) (Bornology.cobounded ℂ) (𝓝 ∞) := by
      simpa only [coclosedCompact_eq_cocompact,Metric.cobounded_eq_cocompact] using
        (OnePoint.tendsto_coe_infty (X:=ℂ))
    apply (hc.comp Filter.tendsto_inv₀_nhdsNE_zero).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (inversion_coe hx).symm
  · apply (OnePoint.continuous_coe.continuousAt.comp (continuousAt_id.inv₀ ht)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht] with x hx
    exact inversion_coe hx

theorem inversion_continuous : Continuous inversion := by
  apply (OnePoint.continuous_iff inversion).mpr
  constructor
  · rw [inversion_infty,coclosedCompact_eq_cocompact,←Metric.cobounded_eq_cocompact]
    apply (OnePoint.continuous_coe.continuousAt.tendsto.comp Filter.tendsto_inv₀_cobounded).congr'
    filter_upwards [Bornology.eventually_ne_cobounded (0:ℂ)] with x hx
    exact (inversion_coe hx).symm
  · exact continuous_iff_continuousAt.mpr coe_inversion_continuousAt

@[expose] def inversionHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toEquiv := ⟨inversion,inversion,inversion_involutive,inversion_involutive⟩
  continuous_toFun := inversion_continuous
  continuous_invFun := inversion_continuous

lemma inversionHomeomorph_apply (z : OnePoint ℂ) : inversionHomeomorph z=inversion z := rfl

end SphereInversion318
