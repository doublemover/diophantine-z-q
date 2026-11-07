module
public import GammaOneFiber318
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public section
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups
namespace RotatedWidths318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Actual integer translations in the conjugate g⁻¹ Gamma1(N) g. -/
@[expose] def periods (N:ℕ) (g:SL(2,ℤ)) : AddSubgroup ℤ where
  carrier := {n | g*ModularGroup.T^n*g⁻¹∈CongruenceSubgroup.Gamma1 N}
  zero_mem' := by
    change g*ModularGroup.T^(0:ℤ)*g⁻¹∈CongruenceSubgroup.Gamma1 N
    simp only [zpow_zero,mul_one,mul_inv_cancel]
    exact (CongruenceSubgroup.Gamma1 N).one_mem
  add_mem' {m n} hm hn := by
    change g*ModularGroup.T^(m+n)*g⁻¹∈CongruenceSubgroup.Gamma1 N
    simpa only [zpow_add,mul_assoc,inv_mul_cancel_left] using
      (CongruenceSubgroup.Gamma1 N).mul_mem hm hn
  neg_mem' {n} hn := by
    change g*ModularGroup.T^(-n)*g⁻¹∈CongruenceSubgroup.Gamma1 N
    simpa only [mul_inv_rev,inv_inv,←zpow_neg,mul_assoc] using
      (CongruenceSubgroup.Gamma1 N).inv_mem hn

theorem level_mem_periods (N:ℕ) (g:SL(2,ℤ)) : (N:ℤ)∈periods N g := by
  have ht:ModularGroup.T^(N:ℤ)∈CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N:ℤ) (N:ℤ) (dvd_refl _)
  have hc := (CongruenceSubgroup.Gamma_normal N).conj_mem _ ht g
  change g*ModularGroup.T^(N:ℤ)*g⁻¹∈CongruenceSubgroup.Gamma1 N
  simpa only [CongruenceSubgroup.Gamma1_mem] using
    ⟨(CongruenceSubgroup.Gamma_mem.mp hc).1,
      (CongruenceSubgroup.Gamma_mem.mp hc).2.2.2,
      (CongruenceSubgroup.Gamma_mem.mp hc).2.2.1⟩

/-- A positive actual width, dividing the level, with the full exact stabilizer-period law. -/
theorem exists_width (N:ℕ) (hN:0<N) (g:SL(2,ℤ)) :
    ∃w:ℕ,0<w ∧ w∣N ∧ ∀n:ℤ,n∈periods N g ↔ (w:ℤ)∣n := by
  obtain ⟨a,ha⟩ := (periods N g).isAddCyclic_iff_exists_zmultiples_eq_top.mp
    (Int.subgroup_cyclic (periods N g))
  have hNa:(a:ℤ)∣N := by
    rw [←Int.mem_zmultiples_iff,ha]
    exact level_mem_periods N g
  have ha0:a≠0 := by
    intro hz;rw [hz,zero_dvd_iff] at hNa
    exact (Nat.ne_of_gt hN) (by exact_mod_cast hNa)
  refine ⟨a.natAbs,Int.natAbs_pos.mpr ha0,?_,?_⟩
  · exact_mod_cast (Int.natAbs_dvd.mpr hNa)
  · intro n
    rw [←ha,←Int.zmultiples_natAbs a,Int.mem_zmultiples_iff]

@[expose] def width (N:ℕ) (hN:0<N) (g:SL(2,ℤ)) : ℕ := (exists_width N hN g).choose

theorem width_positive (N:ℕ) (hN:0<N) (g:SL(2,ℤ)) : 0<width N hN g :=
  (exists_width N hN g).choose_spec.1

theorem width_dvd_level (N:ℕ) (hN:0<N) (g:SL(2,ℤ)) : width N hN g∣N :=
  (exists_width N hN g).choose_spec.2.1

theorem width_le_level (N:ℕ) (hN:0<N) (g:SL(2,ℤ)) : width N hN g≤N :=
  Nat.le_of_dvd hN (width_dvd_level N hN g)

theorem period_iff (N:ℕ) (hN:0<N) (g:SL(2,ℤ)) (n:ℤ) :
    g*ModularGroup.T^n*g⁻¹∈CongruenceSubgroup.Gamma1 N ↔ (width N hN g:ℤ)∣n :=
  (exists_width N hN g).choose_spec.2.2 n

end RotatedWidths318
