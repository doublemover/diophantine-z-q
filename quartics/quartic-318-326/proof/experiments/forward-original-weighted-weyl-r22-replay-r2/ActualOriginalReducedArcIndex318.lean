module
public import ActualOriginalFullFiveLogarithmicBound318
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.RingTheory.Int.Basic
public section
noncomputable section
namespace ActualOriginalReducedArcIndex318
open ActualOriginalMajorArcDomain318

/-- A canonical reduced INTEGER fraction is an actual unit-numerator major
arc index, including 0/1. No different family of rational arcs is substituted. -/
theorem actual_reduced_arc_index (N : ℕ) (a q : ℤ) (hq : 0<q)
    (hqN : q≤N) (ha : 0≤a) (haq : a<q) (hc : IsCoprime q a) :
    ∃ i : ArcIndex N, center i=(a : ℝ)/(q : ℝ) := by
  have hqn : 0<q.toNat := by omega
  have hqnN : q.toNat≤N := by omega
  have han : a.toNat<q.toNat := by omega
  have hqa : Nat.Coprime a.toNat q.toNat := by
    have hh := Int.isCoprime_iff_nat_coprime.mp hc.symm
    rw [←Int.toNat_of_nonneg ha,←Int.toNat_of_nonneg hq.le] at hh
    simpa only [Int.natAbs_natCast] using hh
  let k : Fin N := ⟨q.toNat-1,by omega⟩
  have hk : k.val+1=q.toNat := by dsimp [k]; omega
  let z : ZMod (k.val+1) := (a.toNat : ZMod (k.val+1))
  have hz : IsUnit z := by
    apply (ZMod.isUnit_iff_coprime a.toNat (k.val+1)).mpr
    simpa only [hk] using hqa
  have hzv : z.val=a.toNat := by
    change (a.toNat : ZMod (k.val+1)).val=a.toNat
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨k,⟨z,hz⟩⟩,?_⟩
  change (z.val : ℝ)/(k.val+1 : ℕ)=(a : ℝ)/(q : ℝ)
  rw [hzv,hk]
  have hanR : (a.toNat : ℝ)=(a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha
  have hqnR : (q.toNat : ℝ)=(q : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hq.le
  rw [hanR,hqnR]

end ActualOriginalReducedArcIndex318
