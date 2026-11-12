module
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic
public section
noncomputable section
namespace ConformalBoundaryModulus318
open Set Metric Filter
open scoped Topology ComplexConjugate
set_option maxHeartbeats 2400000
abbrev UnitDisk := ball (0:ℂ) 1

/-- Compact subdisks remain compact INSIDE the open disk, rather than
merely compact after an unproved boundary extension. -/
theorem inner_subdisk_compact (r : ℝ) (hr : r<1) :
    IsCompact {w : UnitDisk | ‖w.val‖≤r} := by
  rw [Subtype.isCompact_iff]
  have he : (Subtype.val : UnitDisk → ℂ) '' {w : UnitDisk | ‖w.val‖≤r}=closedBall (0:ℂ) r := by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      simpa only [Set.mem_setOf_eq,mem_closedBall,dist_zero_right] using hz
    · intro hw
      have hnorm : ‖w‖≤r := by simpa only [mem_closedBall,dist_zero_right] using hw
      refine ⟨⟨w,?_⟩,hnorm,rfl⟩
      simpa only [mem_ball,dist_zero_right] using lt_of_le_of_lt hnorm hr
  rw [he]
  exact isCompact_closedBall _ _

/-- Properness at each ORIGINAL domain boundary point, constructed from
an actual homeomorphism onto the disk. This does not assume any limiting
complex value or any Caratheodory boundary extension. -/
theorem boundary_norm_lower (U : Set ℂ) (hU : IsOpen U) (e : U ≃ₜ UnitDisk)
    (f : ℂ → ℂ) (hf : ∀z : U,f z=(e z).val) (x : ℂ) (hx : x∈frontier U)
    (r : ℝ) (hr : r<1) : ∀ᶠz in 𝓝[U] x,r<‖f z‖ := by
  let K : Set UnitDisk := {w | ‖w.val‖≤r}
  let C : Set ℂ := (Subtype.val : U → ℂ) '' (e.symm '' K)
  have hC : IsCompact C :=
    ((inner_subdisk_compact r hr).image e.symm.continuous).image continuous_subtype_val
  have hxU : x∉U := by
    have hh := hx.2
    rwa [hU.interior_eq] at hh
  have hxC : x∉C := by
    rintro ⟨z,hz,hzx⟩
    exact hxU (hzx ▸ z.property)
  have hnb : Cᶜ∈𝓝 x := hC.isClosed.isOpen_compl.mem_nhds hxC
  filter_upwards [nhdsWithin_le_nhds hnb,self_mem_nhdsWithin] with z hzC hzU
  by_contra hn
  have hnorm : ‖f z‖≤r := le_of_not_gt hn
  apply hzC
  let q : U := ⟨z,hzU⟩
  refine ⟨q,⟨e q,?_,e.symm_apply_apply q⟩,rfl⟩
  change ‖(e q).val‖≤r
  simpa only [←hf q] using hnorm

theorem boundary_norm_tendsto_one (U : Set ℂ) (hU : IsOpen U) (e : U ≃ₜ UnitDisk)
    (f : ℂ → ℂ) (hf : ∀z : U,f z=(e z).val) (x : ℂ) (hx : x∈frontier U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] x) (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro r hr
    exact boundary_norm_lower U hU e f hf x hx r hr
  · intro r hr
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hh : ‖f z‖<1 := by
      rw [hf ⟨z,hz⟩]
      simpa only [mem_ball,dist_zero_right] using (e ⟨z,hz⟩).property
    exact hh.trans hr

/-- The actual upper/lower reflected boundary jump is controlled by
modulus alone. It can tend to zero even before a complex boundary value
has been constructed. -/
theorem reflected_jump_norm (w : ℂ) :
    ‖w-(conj w)⁻¹‖=|‖w‖^2-1|/‖w‖ := by
  by_cases hw : w=0
  · subst w; norm_num
  have hc : conj w≠0 := by simpa using hw
  have hid : w-(conj w)⁻¹=(((Complex.normSq w-1:ℝ):ℂ))/(conj w) := by
    apply (eq_div_iff hc).mpr
    rw [sub_mul,inv_mul_cancel₀ hc,Complex.mul_conj]
    push_cast <;> rfl
  rw [hid,norm_div,Complex.norm_real,Complex.norm_conj,Complex.normSq_eq_norm_sq]
  exact congrArg (fun t : ℝ => t/‖w‖) (Real.norm_eq_abs _)

theorem reflected_jump_tendsto_zero {X : Type*} (l : Filter X) (f : X → ℂ)
    (h : Tendsto (fun z => ‖f z‖) l (𝓝 1)) :
    Tendsto (fun z => f z-(conj (f z))⁻¹) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [reflected_jump_norm]
  have hconst : Tendsto (fun _ : X => (1:ℝ)) l (𝓝 (1:ℝ)) := tendsto_const_nhds
  have hh : Tendsto (fun z => |‖f z‖^2-1|/‖f z‖) l (𝓝 (|(1:ℝ)^2-1|/1)) :=
    ((h.pow 2).sub hconst).abs.div h (by norm_num : (1:ℝ)≠0)
  simpa using hh
end ConformalBoundaryModulus318
