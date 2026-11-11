module
public import OvalFlowAddition318
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.Group.Quotient
public section
noncomputable section

/-! The exact invariant-clock period is the complete kernel of the actual
additive flow. The resulting circle comparison is both additive and a
homeomorphism in the original real subspace topology. -/
namespace OvalAddCircle318
open RealQuarticGroup318 OvalInvariantClock318 OvalFlowAddition318
local instance : AddCommGroup (Oval 1) := group 1 (by norm_num)
local instance : Fact (0<period) := ⟨period_pos⟩
set_option maxHeartbeats 2000000

lemma clock_zsmul (n : ℤ) : clock (n • (2*Real.pi))=n • period := by
  simpa only [clock,period,_root_.zero_add] using
    speed_periodic.intervalIntegral_add_zsmul_eq n 0
      (fun a b => speed_continuous.intervalIntegrable a b)

/-- Both directions use the original full oval. The second u=0 point has
v=-1 and is correctly not in the kernel of this parametrization. -/
theorem flow_eq_zero_iff (s : ℝ) : flow s=(0:Oval 1) ↔ ∃ n : ℤ, n • period=s := by
  constructor
  · intro he
    have hu := congrArg (fun p : Oval 1 => p.val.1) he
    have hv := congrArg (fun p : Oval 1 => p.val.2) he
    change Real.sin (angle s)=0 at hu
    change RealQuarticOvalCover318.v (angle s)=1 at hv
    have hc : Real.cos (angle s)=1 := by
      simpa [RealQuarticOvalCover318.v,hu] using hv
    obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff (angle s)).mp hc
    refine ⟨n,?_⟩
    calc
      n • period=clock (n • (2*Real.pi)) := (clock_zsmul n).symm
      _ = clock (angle s) := congrArg clock (by simpa [zsmul_eq_mul] using hn)
      _ = s := clock_angle s
  · rintro ⟨n,rfl⟩
    have he := (flow_periodic.zsmul n) 0
    have hz : flow 0=(0:Oval 1) := Subtype.ext flow_zero
    simpa only [_root_.zero_add,hz] using he

lemma kernel_eq : AddSubgroup.zmultiples period=flowHom.ker := by
  ext s
  change (∃ n : ℤ, n • period=s) ↔ flow s=(0:Oval 1)
  exact (flow_eq_zero_iff s).symm

/-- The group law on the target is exactly RealQuarticGroup318.group, not
a newly transported group operation chosen to agree with this map. -/
@[expose] def circleAddEquiv : AddCircle period ≃+ Oval 1 :=
  QuotientAddGroup.liftEquiv (AddSubgroup.zmultiples period) (φ:=flowHom)
    flow_surjective kernel_eq

lemma circleAddEquiv_coe (s : ℝ) : circleAddEquiv (s : AddCircle period)=flow s := rfl

lemma circleAddEquiv_continuous : Continuous circleAddEquiv := by
  have hq : Topology.IsQuotientMap (fun s : ℝ => (s : AddCircle period)) :=
    isQuotientMap_quotient_mk'
  exact hq.continuous_iff.mpr flow_continuous

/-- Compactness of the genuine additive circle and Hausdorffness of the
original oval topology upgrade the actual continuous group equivalence. -/
@[expose] def circleHomeomorph : AddCircle period ≃ₜ Oval 1 :=
  circleAddEquiv.toEquiv.toHomeomorphOfContinuousClosed circleAddEquiv_continuous
    circleAddEquiv_continuous.isClosedMap

lemma circleHomeomorph_coe (s : ℝ) : circleHomeomorph (s : AddCircle period)=flow s := rfl

end OvalAddCircle318
