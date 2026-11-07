module
public import TorusInjective318
public import Mathlib.Analysis.Complex.Liouville
public section
noncomputable section
open Filter Set
open scoped Topology
namespace WeierstrassSurjective318
set_option maxHeartbeats 0
attribute [local instance] Classical.propDecidable

/-- Reciprocal of ℘−c, with the removable zeros at the actual lattice points filled in. -/
@[expose] def reciprocal (L : PeriodPair) (c z : ℂ) : ℂ :=
  if z ∈ L.lattice then 0 else (L.weierstrassP z - c)⁻¹

lemma reciprocal_zero (L : PeriodPair) (c : ℂ) : reciprocal L c 0 = 0 := by
  simp [reciprocal]

lemma reciprocal_add_period (L : PeriodPair) (c z : ℂ) (l : L.lattice) :
    reciprocal L c (z+l) = reciprocal L c z := by
  have hm : z+(l:ℂ) ∈ L.lattice ↔ z ∈ L.lattice := add_mem_cancel_right l.property
  simp only [reciprocal, hm, L.weierstrassP_add_coe]

lemma reciprocal_analytic_zero (L : PeriodPair) (c : ℂ) : AnalyticAt ℂ (reciprocal L c) 0 := by
  have he : AnalyticAt ℂ (L.weierstrassPExcept 0) 0 := L.analyticAt_weierstrassPExcept 0
  have ha : AnalyticAt ℂ
      (fun z : ℂ => z^2 / (1 + z^2 * (L.weierstrassPExcept 0 z - c))) 0 := by
    fun_prop (disch := norm_num)
  apply ha.congr
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases hz0 : z = 0
  · simp [hz0, reciprocal_zero]
  · have hn : z ∉ L.lattice := by
      simp only [mem_compl_iff, Set.mem_sdiff, SetLike.mem_coe, mem_singleton_iff] at hz
      exact fun h => hz ⟨h,hz0⟩
    rw [reciprocal, ite_eq_right hn]
    have hp := L.weierstrassPExcept_add (0 : L.lattice) z
    simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero] at hp
    have hden : 1 + z^2*(L.weierstrassPExcept 0 z-c) = z^2*(L.weierstrassP z-c) := by
      rw [← hp]
      field_simp
      ring
    rw [hden, div_mul_eq_div_div, div_self (pow_ne_zero 2 hz0)]
    simp only [one_div]

lemma reciprocal_analytic (L : PeriodPair) (c : ℂ)
    (homit : ∀ z, z ∉ L.lattice → L.weierstrassP z ≠ c) (z : ℂ) :
    AnalyticAt ℂ (reciprocal L c) z := by
  by_cases hz : z ∈ L.lattice
  · have hzero := reciprocal_analytic_zero L c
    have hza : AnalyticAt ℂ (reciprocal L c) (z-z) := by simpa using hzero
    have ha := hza.comp (f := fun w : ℂ => w-z) (by fun_prop)
    convert ha using 1
    funext w
    have hperiod := reciprocal_add_period L c (w-z) ⟨z,hz⟩
    simpa using hperiod
  · have ha : AnalyticAt ℂ (fun w => (L.weierstrassP w-c)⁻¹) z :=
      ((L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const).inv (sub_ne_zero.mpr (homit z hz))
    apply ha.congr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    change w ∉ L.lattice at hw
    simp [reciprocal, hw]

/-- The actual ℘-function takes every complex value at a non-lattice point.
This uses the genuine removable reciprocal and Liouville, not a degree theorem. -/
theorem exists_value (L : PeriodPair) (c : ℂ) :
    ∃ z : ℂ, z ∉ L.lattice ∧ L.weierstrassP z = c := by
  by_contra hh
  push Not at hh
  have hd : Differentiable ℂ (reciprocal L c) :=
    fun z => (reciprocal_analytic L c hh z).differentiableAt
  have hb : Bornology.IsBounded (Set.range (reciprocal L c)) :=
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hd.continuous
      (fun z w hw => reciprocal_add_period L c z ⟨w,hw⟩)).isBounded
  have hz := hd.apply_eq_apply_of_bounded hb (L.ω₁/2) 0
  rw [reciprocal_zero, reciprocal, ite_eq_right L.ω₁_div_two_notMem_lattice] at hz
  exact hh (L.ω₁/2) L.ω₁_div_two_notMem_lattice (sub_eq_zero.mp (inv_eq_zero.mp hz))

end WeierstrassSurjective318
