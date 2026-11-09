module
public import ActualThreeCuspOrbit318
public import CuspOrbit318
public import GammaHCuspWidths318
public section
noncomputable section
open scoped MatrixGroups
namespace ActualThreeCuspWidths318
open RotatedWidths318
set_option maxHeartbeats 0

/-- Every genuine conjugate cusp width at level three is one or three. -/
theorem width_one_or_three (g : SL(2,ℤ)) :
    width 3 (by decide) g=1 ∨ width 3 (by decide) g=3 :=
  (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (width_dvd_level 3 (by decide) g)

/-- The original standard infinity cusp has actual width one. -/
theorem width_identity : width 3 (by decide) 1=1 := by
  have hm : (1:ℤ) ∈ periods 3 1 := by
    change 1*ModularGroup.T^(1:ℤ)*1⁻¹ ∈ CongruenceSubgroup.Gamma1 3
    simpa only [one_mul,mul_one,inv_one] using CuspOrbit318.translation_mem 3 1
  have hd : (width 3 (by decide) 1:ℤ) ∣ 1 :=
    (period_iff 3 (by decide) 1 1).mp hm
  have hd' : width 3 (by decide) 1 ∣ 1 := by exact_mod_cast hd
  exact Nat.eq_one_of_dvd_one hd'

/-- The original S-rotated cusp has actual width three. This is computed
from Gamma1(3) matrix membership rather than inferred from rational J orders. -/
theorem width_S : width 3 (by decide) ModularGroup.S=3 := by
  rcases width_one_or_three ModularGroup.S with hw | hw
  · have hm : ModularGroup.S*ModularGroup.T^(1:ℤ)*ModularGroup.S⁻¹ ∈
        CongruenceSubgroup.Gamma1 3 :=
      (period_iff 3 (by decide) ModularGroup.S 1).mpr (by rw [hw]; simp)
    norm_num [CongruenceSubgroup.Gamma1_mem,ModularGroup.S_inv,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_neg,
      ModularGroup.coe_T_zpow,ModularGroup.coe_S,Matrix.mul_fin_two] at hm
  · exact hw

/-- These are genuinely different cusp ends in the original quotient. -/
theorem neighborhoods_distinct :
    RotatedProjection318.neighborhood 3 1 ≠
      RotatedProjection318.neighborhood 3 ModularGroup.S := by
  intro he
  have hw := GammaHCuspWidths318.width_of_periods_eq 3 (by decide) 1 ModularGroup.S
    (GammaHCuspWidths318.periods_of_neighborhood_eq 3 1 ModularGroup.S he)
  rw [width_identity,width_S] at hw
  norm_num at hw

theorem neighborhoods_disjoint :
    Disjoint (RotatedProjection318.neighborhood 3 1)
      (RotatedProjection318.neighborhood 3 ModularGroup.S) :=
  (RotatedEndSeparation318.neighborhoods_equal_or_disjoint 3 1 ModularGroup.S).resolve_left neighborhoods_distinct

end ActualThreeCuspWidths318
