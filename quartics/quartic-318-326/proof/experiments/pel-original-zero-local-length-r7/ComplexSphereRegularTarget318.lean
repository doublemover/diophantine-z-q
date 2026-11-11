module
public import PELActualInteriorSphereMap318
public import Mathlib.Topology.Closure
public section
noncomputable section
namespace ComplexSphereRegularTarget318
open Set Metric Filter Complex
open scoped Topology OnePoint
open ReflectedDiskJoukowski318 PELActualInteriorSphereMap318
open PELMaximalActualComplexDomain318
set_option maxHeartbeats 2400000

/-- A concrete dense target region avoiding the ENTIRE seam image. -/
@[expose] def regular : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' {w | w.re≠0}

lemma dense_nonzero_real : Dense {w : ℂ | w.re≠0} := by
  apply dense_iff_inter_open.mpr
  intro O hO hne
  obtain ⟨w,hw⟩ := hne
  by_cases hr : w.re=0
  · obtain ⟨r,hr0,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hw)
    refine ⟨w+(r/2:ℝ),hball ?_,?_⟩
    · rw [Metric.mem_ball,dist_eq_norm]
      simp only [add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (half_pos hr0)]
      linarith
    · change (w+(r/2:ℝ)).re≠0
      simp only [Complex.add_re,Complex.ofReal_re,hr,zero_add]
      exact (half_pos hr0).ne'
  · exact ⟨w,hw,hr⟩

/-- Density includes the original point at infinity; this is not merely
density inside one affine chart. -/
theorem regular_dense : Dense regular := by
  apply dense_iff_inter_open.mpr
  intro O hO hne
  obtain ⟨p,hp,⟨w,rfl⟩⟩ :=
    (OnePoint.denseRange_coe (X:=ℂ)).inter_open_nonempty O hO hne
  obtain ⟨z,hz,hzr⟩ := dense_nonzero_real.inter_open_nonempty
    (((↑):ℂ→OnePoint ℂ) ⁻¹' O) (hO.preimage OnePoint.continuous_coe) ⟨w,hp⟩
  exact ⟨(z:OnePoint ℂ),hz,⟨z,hzr,rfl⟩⟩

theorem unit_boundary_not_regular (z : ℂ) (hz : ‖z‖=1) : joukowski z∉regular := by
  have hz0 : z≠0 := by intro he; rw [he,norm_zero] at hz; norm_num at hz
  rintro ⟨w,hw,hwe⟩
  have hwe' : w=z-z⁻¹ := by
    apply OnePoint.coe_injective
    simpa only [joukowski,if_neg hz0] using hwe
  apply hw
  rw [hwe',inverse_on_circle z hz]
  simp

/-- Every point of the actual dense regular target has a STRICT interior
preimage under the same Joukowski map, not just a closed-disk preimage. -/
theorem regular_interior_cover (p : OnePoint ℂ) (hp : p∈regular) :
    ∃ z : ℂ,‖z‖<1 ∧ joukowski z=p := by
  obtain ⟨w,hw,rfl⟩ := hp
  obtain ⟨z,hz,hz0,hzw⟩ := quadratic_root_in_disk w
  have hzp : joukowski z=(w:OnePoint ℂ) := by simp only [joukowski,if_neg hz0,hzw]
  have hne : ‖z‖≠1 := by
    intro hh
    exact unit_boundary_not_regular z hh (hzp.symm ▸ (show (w:OnePoint ℂ)∈regular from ⟨w,hw,rfl⟩))
  exact ⟨z,lt_of_le_of_ne hz hne,hzp⟩

/-- The genuine original conformal chart covers that same dense regular
sphere region. No compact-boundary extension is needed for this coverage. -/
theorem actual_interior_cover (e : OpenPartialHomeomorph ℂ ℂ)
    (hs : e.source=openDomain) (ht : e.target=ball 0 1)
    (p : OnePoint ℂ) (hp : p∈regular) : ∃ z∈openDomain,sphereMap e z=p := by
  obtain ⟨w,hw,hwp⟩ := regular_interior_cover p hp
  have hwt : w∈e.target := by rw [ht]; simpa only [mem_ball,dist_zero_right] using hw
  refine ⟨e.symm w,hs ▸ e.map_target hwt,?_⟩
  change joukowski (e (e.symm w))=p
  rw [e.right_inv hwt]
  exact hwp
end ComplexSphereRegularTarget318
