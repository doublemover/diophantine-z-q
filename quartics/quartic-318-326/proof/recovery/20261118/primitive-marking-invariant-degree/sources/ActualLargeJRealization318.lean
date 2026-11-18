module
public import LargeJActualOrbit318
public import HighQParameter318
public section
noncomputable section
namespace ActualLargeJRealization318
open Filter Topology Metric Function UpperHalfPlane ActualJCusp318 ReciprocalCuspCoordinate318

/-- Every sufficiently large complex value actually IS attained, proved
using the genuine inverse of reciprocal-j at the cusp and exponential
uniformization of a punctured disc, not the global classification of
complex elliptic curves by periods. -/
theorem all_large : ∃M:ℝ, ∀c:ℂ,M<‖c‖ →
    ∃τ:UpperHalfPlane,ActualQJ318.jInvariant τ=c := by
  have hpos := HighQParameter318.radius_positive 2
  have hc : ContinuousAt inverseGerm 0 := inverseGerm_analytic.continuousAt
  have hv : ∀ᶠ s in 𝓝 (0:ℂ), ‖inverseGerm s‖<HighQParameter318.radius 2 :=
    hc.norm.eventually_lt continuousAt_const (by simpa [inverseGerm_zero] using hpos)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (inverseGerm_right.and hv)
  refine ⟨ε⁻¹,?_⟩
  intro c hlarge
  have hcpos : 0<‖c‖ := (inv_pos.mpr hε).trans hlarge
  have hcz : c≠0 := norm_pos_iff.mp hcpos
  have hsmall : c⁻¹∈ball 0 ε := by
    rw [mem_ball_zero_iff,norm_inv]
    calc ‖c‖⁻¹ < (ε⁻¹)⁻¹ := (inv_lt_inv₀ hcpos (inv_pos.mpr hε)).mpr hlarge
         _ = ε := inv_inv _
  obtain ⟨hrec,hnorm⟩ := hball hsmall
  let q := inverseGerm c⁻¹
  have hn : q≠0 := by
    intro hh
    have hq : reciprocalGerm q=c⁻¹ := hrec
    rw [hh,reciprocalGerm_zero] at hq
    exact (inv_ne_zero hcz) hq.symm
  let v : HighQParameter318.punctured 2 := ⟨q,hn,hnorm⟩
  obtain ⟨t,ht⟩ := HighQParameter318.qMap_surjective 2 (by norm_num) v
  have eq : Periodic.qParam 1 t.val=q := congrArg Subtype.val ht
  refine ⟨t.val,inv_injective ?_⟩
  rw [←reciprocalGerm_qParam,eq]
  exact hrec
end ActualLargeJRealization318
