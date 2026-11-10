module
public import ComplexLineHolomorphicLift318
public import Mathlib.Topology.LocallyConstant.Basic
public section
noncomputable section
namespace ComplexLineLiftDerivative318
open ComplexLineLatticeAtlas318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 3000000
variable (L : AddSubgroup ℂ) [DiscreteTopology L]
variable (f : Quotient L→Quotient L) (F : ℂ→ℂ)
variable (hF : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F)
variable (hlift : ∀ z,projection L (F z)=f (projection L z))

include f hF hlift in
/-- Actual period increments of an entire lift lie in the SAME discrete
lattice. Connectedness of C forces each increment to be constant. -/
theorem period_increment (a : L) (z : ℂ) :
    F (z+a.val)-F z=F a.val-F 0 := by
  have hmem (w : ℂ) : F (w+a.val)-F w∈L := by
    apply (QuotientAddGroup.eq_zero_iff).mp
    change (QuotientAddGroup.mk' L) (F (w+a.val)-F w)=0
    rw [map_sub]
    change projection L (F (w+a.val))-projection L (F w)=0
    rw [hlift,hlift]
    have ha : projection L (w+a.val)=projection L w := by
      change (QuotientAddGroup.mk' L) (w+a.val)=(QuotientAddGroup.mk' L) w
      rw [map_add,show (QuotientAddGroup.mk' L) a.val=0 from
        (QuotientAddGroup.eq_zero_iff).mpr a.property,add_zero]
    rw [ha,sub_self]
  let D : ℂ→L := fun w => ⟨F (w+a.val)-F w,hmem w⟩
  have hc : Continuous D :=
    ((hF.continuous.comp (continuous_id.add continuous_const)).sub hF.continuous).subtype_mk _
  have he := ((IsLocallyConstant.iff_continuous D).mpr hc).apply_eq_of_preconnectedSpace z 0
  simpa only [D,zero_add] using congrArg Subtype.val he

include f hF hlift in
/-- The derivative of the lift is genuinely L-periodic, for all periods
and all complex arguments, before compactness or Liouville is used. -/
theorem derivative_periodic (a : L) (z : ℂ) : deriv F (z+a.val)=deriv F z := by
  have hd (w : ℂ) : DifferentiableAt ℂ F w :=
    (contMDiffAt_iff_contDiffAt.mp (hF w)).analyticAt.differentiableAt
  have he : (fun w : ℂ => F (w+a.val))=(fun w => F w+(F a.val-F 0)) := by
    funext w
    have h := period_increment L f F hF hlift a w
    linear_combination h
  have hleft : HasDerivAt (fun w : ℂ => F (w+a.val)) (deriv F (z+a.val)) z := by
    simpa only [mul_one] using (hd (z+a.val)).hasDerivAt.comp z ((hasDerivAt_id z).add_const a.val)
  have hright : HasDerivAt (fun w : ℂ => F (w+a.val)) (deriv F z) z := by
    rw [he]
    exact (hd z).hasDerivAt.add_const _
  exact hleft.unique hright

include f hF hlift in
/-- Derivative equality descends through the exact original period
quotient relation, not an assumed bounded fundamental parallelogram. -/
theorem derivative_same_fiber (z w : ℂ) (he : projection L z=projection L w) :
    deriv F z=deriv F w := by
  have hm : z-w∈L := by
    apply (QuotientAddGroup.eq_zero_iff).mp
    change (QuotientAddGroup.mk' L) (z-w)=0
    rw [map_sub]
    exact sub_eq_zero.mpr he
  have hd := derivative_periodic L f F hF hlift ⟨z-w,hm⟩ w
  have hz : w+(z-w)=z := by abel
  simpa only [hz] using hd

@[expose] def quotientDerivative : Quotient L→ℂ :=
  Quotient.lift (deriv F) (fun z w h => derivative_same_fiber L f F hF hlift z w (Quotient.sound h))

theorem quotientDerivative_continuous : Continuous (quotientDerivative L f F hF hlift) := by
  have hc : Continuous (deriv F) := continuous_iff_continuousAt.mpr (fun z =>
    (contMDiffAt_iff_contDiffAt.mp (hF z)).analyticAt.deriv.continuousAt)
  exact hc.quotient_lift _
end ComplexLineLiftDerivative318
