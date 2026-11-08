module
public import AnalyticScalingGerm318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ScaledCoordinateGerm318
open PeriodEisenstein318 LatticeInvariants318 InfinityAnalyticChart318
set_option maxHeartbeats 0

lemma tendsto_puncture {w : ℂ → ℂ} {a : ℂ} (hw : AnalyticAt ℂ w 0)
    (hw0 : w 0=0) (hD : HasDerivAt w a 0) (ha : a≠0) :
    Tendsto w (𝓝[≠] 0) (𝓝[≠] 0) := by
  obtain ⟨g,hg,hg0,hl,hr⟩ := FiniteAnalyticCharts318.analytic_inverse hw
    (by rw [hD.deriv]; exact ha)
  rw [hw0] at hg0
  have hn : ∀ᶠ z in 𝓝[≠] (0:ℂ), w z≠0 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hl,self_mem_nhdsWithin] with z hz hzn
    intro hzero
    have hz0 : z=0 := by simpa only [hzero,hg0,id_eq] using hz.symm
    exact hzn hz0
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_,hn⟩
  have ht : Tendsto w (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt,hw0] using hw.continuousAt
  exact ht.mono_left nhdsWithin_le_nhds

lemma coordinates_of_ratios (u : ℂˣ) (x y x' y' : ℂ) (hy : y≠0) (hy' : y'≠0)
    (ht : -x'/y'=(u:ℂ)⁻¹*(-x/y))
    (hv : 1/y'=((u:ℂ)⁻¹)^3*(1/y)) :
    x'=(u:ℂ)^2*x ∧ y'=(u:ℂ)^3*y := by
  have hu : (u:ℂ)≠0 := Units.ne_zero u
  have hey : y'=(u:ℂ)^3*y := by
    calc
      y'=(1/y')⁻¹ := by simp
      _=(((u:ℂ)⁻¹)^3*(1/y))⁻¹ := congrArg (fun z : ℂ => z⁻¹) hv
      _=(u:ℂ)^3*y := by simp [mul_inv_rev,mul_comm]
  refine ⟨?_,hey⟩
  calc
    x'=(-x'/y')*(-y') := by field_simp
    _=((u:ℂ)⁻¹*(-x/y))*(-((u:ℂ)^3*y)) := by rw [ht,hey]
    _=(u:ℂ)^2*x := by field_simp <;> ring

/-- Actual normalized Weierstrass coordinate germs under the constructed lift.
The lift is holomorphic, but its linearity is not part of this theorem. -/
theorem exists_coordinate_germ (tau sigma : UpperHalfPlane) (u : ℂˣ)
    (h4 : (ModularWeierstrass318.curve sigma).a₄=
      (u:ℂ)^4*(ModularWeierstrass318.curve tau).a₄)
    (h6 : (ModularWeierstrass318.curve sigma).a₆=
      (u:ℂ)^6*(ModularWeierstrass318.curve tau).a₆) :
    ∃ w : ℂ → ℂ, AnalyticAt ℂ w 0 ∧ w 0=0 ∧ HasDerivAt w (u:ℂ)⁻¹ 0 ∧
      (fun z => xCoord sigma (w z)) =ᶠ[𝓝 0] (fun z => (u:ℂ)^2*xCoord tau z) ∧
      (fun z => yCoord sigma (w z)) =ᶠ[𝓝 0] (fun z => (u:ℂ)^3*yCoord tau z) := by
  obtain ⟨w,hw,hw0,hD,ht,hv⟩ := AnalyticScalingGerm318.exists_scaling_germ tau sigma u h4 h6
  have hwt := tendsto_puncture hw hw0 hD (inv_ne_zero (Units.ne_zero u))
  have he : ∀ᶠ z in 𝓝[≠] (0:ℂ),
      xCoord sigma (w z)=(u:ℂ)^2*xCoord tau z ∧
      yCoord sigma (w z)=(u:ℂ)^3*yCoord tau z := by
    filter_upwards [coordinates_eventually tau,hwt.eventually (coordinates_eventually sigma),
      mem_nhdsWithin_of_mem_nhds ht,mem_nhdsWithin_of_mem_nhds hv] with z hz hwz htz hvz
    apply coordinates_of_ratios u _ _ _ _ hz.1 hwz.1
    · simpa only [hz.2.1,hwz.2.1] using htz
    · simpa only [hz.2.2,hwz.2.2] using hvz
  have hf : ∀ᶠ z in 𝓝 (0:ℂ),
      xCoord sigma (w z)=(u:ℂ)^2*xCoord tau z ∧
      yCoord sigma (w z)=(u:ℂ)^3*yCoord tau z := by
    filter_upwards [eventually_nhdsWithin_iff.mp he] with z hz
    by_cases hz0 : z=0
    · simp [hz0,hw0,xCoord,yCoord,PeriodPair.weierstrassP_zero,PeriodPair.derivWeierstrassP_zero]
    · exact hz (by simpa using hz0)
  exact ⟨w,hw,hw0,hD,hf.mono (fun _ h => h.1),hf.mono (fun _ h => h.2)⟩

end ScaledCoordinateGerm318
