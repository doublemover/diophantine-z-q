module
public import ActualTwoDescentLiftedKummerClasses318
public section
noncomputable section
namespace ActualTwoDescentGoodPrimeKummerSurjectivity318
set_option maxHeartbeats 16000000

open ActualTwoDescentFiniteKummerSurjectivity318 ActualTwoDescentIntegralPointLiftData318
open ActualTwoDescentAllResiduePointLifts318 ActualTwoDescentLiftedKummerClasses318
open ActualTwoDescentFiniteOriginalCompatibility318 ActualTwoDescentSquareClassQuotient318
variable {p : ℕ} [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Every pair of integral unit classes occurs in the actual original Q_p elliptic Kummer image
at a good prime. This is proved by finite-field group surjectivity and actual point lifting. -/
theorem actual_good_prime_unit_pair (hp2 : p ≠ 2) (hp3 : p ≠ 3) (n a b : ℤ)
    (hn : (n : ZMod p) ≠ 0) (ha : (a : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0) :
    ∃ P : ActualTwoDescentEllipticModel318.Point (n : ℚ_[p]),
      ActualTwoDescentKummerHom318.kummerClass (n : ℚ_[p]) (padic_ne_of_residue hn) P=
        (classOf (a : ℚ_[p]) (padic_ne_of_residue ha),classOf (b : ℚ_[p]) (padic_ne_of_residue hb)) := by
  letI : NeZero (2 : ZMod p) := ⟨(isUnit_iff_ne_zero).mp
    ((ZMod.isUnit_iff_coprime 2 p).mpr
      ((Nat.coprime_primes (by decide : Nat.Prime 2) Fact.out).mpr hp2.symm))⟩
  letI : NeZero (3 : ZMod p) := ⟨(isUnit_iff_ne_zero).mp
    ((ZMod.isUnit_iff_coprime 3 p).mpr
      ((Nat.coprime_primes (by decide : Nat.Prime 3) Fact.out).mpr hp3.symm))⟩
  obtain ⟨P,hP⟩ := actual_finite_kummer_representative (n : ZMod p) hn
    (classOf (a : ZMod p) ha,classOf (b : ZMod p) hb)
  let L := actual_residue_point_lift hp2 n hn P
  refine ⟨L.point,?_⟩
  rw [←actual_same_kummer_class]
  exact actual_lift_kummer_classes hp2 n a b hn ha hb P L hP

/-- The retained beta class is genuinely locally represented at EVERY prime away from6*n*beta. -/
theorem actual_good_prime_beta_image (hp2 : p ≠ 2) (hp3 : p ≠ 3) (n β : ℕ)
    (hn : ¬p ∣ n) (hβ : ¬p ∣ β) :
    ∃ P : ActualTwoDescentEllipticModel318.Point (n : ℚ_[p]),
      ActualTwoDescentKummerHom318.kummerClass (n : ℚ_[p])
        (Nat.cast_ne_zero.mpr (by intro h; apply hn; rw [h]; exact dvd_zero _)) P=
      ActualTwoDescentTorsionKummerValues318.retainedBetaClass (β : ℚ_[p])
        (Nat.cast_ne_zero.mpr (by intro h; apply hβ; rw [h]; exact dvd_zero _)) := by
  have hn' : ((n : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_natCast] using (ZMod.natCast_eq_zero_iff n p).not.mpr hn
  have hβ' : ((β : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_natCast] using (ZMod.natCast_eq_zero_iff β p).not.mpr hβ
  obtain ⟨P,hP⟩ := actual_good_prime_unit_pair hp2 hp3 (n : ℤ) (β : ℤ) 1 hn' hβ' (by simp)
  refine ⟨P,?_⟩
  simpa only [Int.cast_natCast,Int.cast_one,class_of_one,ActualTwoDescentTorsionKummerValues318.retainedBetaClass] using hP

end ActualTwoDescentGoodPrimeKummerSurjectivity318
