module
public import DVRIntegerValue318
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public section
noncomputable section
namespace LenstraVertical318
open Module Algebra IsDiscreteValuationRing Submodule.IsPrincipal

variable (A K B L:Type*) [CommRing A] [IsDomain A] [Field K]
    [CommRing B] [IsDomain B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [Algebra A B] [Algebra B L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [CharZero K] [CharZero A] [CharZero B]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [IsTorsionFree A B]
    [IsFractionRing B L] [IsDiscreteValuationRing B]

/-- The different exponent is the natural-number value of an actual generator
of the actual different ideal. It is independent of the generator choice. -/
@[expose] def differentExponent : ℕ := (addVal B (generator (differentIdeal A B))).toNat

/-- Actual Lenstra bound in mixed residue characteristic. The coefficient is
strictly smaller than v_B(p) times (1+v_p([L:K])). -/
theorem different_exponent_lt (p:ℕ) [Fact p.Prime] (hp:¬IsUnit (p:B)) :
    differentExponent A B <
      (addVal B (p:B)).toNat * (padicValNat p (Module.finrank K L)+1) := by
  have hpA:¬IsUnit (p:A) := by
    intro h
    apply hp
    simpa only [map_natCast] using h.map (algebraMap A B)
  have hp0A:(p:A)≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
  have h:=LenstraDVR318.different_value_lt A K B L (p:A) hp0A hpA
  rw [map_natCast (algebraMap A B),DVRIntegerValue318.value_nat B p (Module.finrank K L) hp
    (Module.finrank_pos (R:=K) (M:=L)).ne'] at h
  have hpf:addVal B (p:B)≠⊤ := by
    intro hz
    have hz0 := (IsDiscreteValuationRing.addVal_eq_top_iff (R:=B)).mp hz
    exact (by exact_mod_cast (Fact.out:p.Prime).ne_zero : (p:B)≠0) hz0
  have hpc:(↑((addVal B (p:B)).toNat):ℕ∞)=addVal B (p:B) := ENat.natCast_toNat hpf
  have hbound:(padicValNat p (Module.finrank K L):ℕ∞)*addVal B (p:B)+addVal B (p:B)=
      ((addVal B (p:B)).toNat * (padicValNat p (Module.finrank K L)+1):ℕ) := by
    conv_lhs => rw [← hpc]
    push_cast
    ring
  rw [hbound] at h
  have hrf:addVal B (generator (differentIdeal A B))≠⊤ := ne_top_of_lt h
  have hrc:(differentExponent A B:ℕ∞)=addVal B (generator (differentIdeal A B)) :=
    ENat.natCast_toNat hrf
  rw [← hrc] at h
  exact_mod_cast h

include K L in
/-- The computed natural exponent is the exponent of the actual maximal-ideal
power defining the different, not a separately chosen valuation model. -/
theorem different_ideal_eq_pow (p:ℕ) [Fact p.Prime] (hp:¬IsUnit (p:B)) :
    differentIdeal A B=IsLocalRing.maximalIdeal B ^ differentExponent A B := by
  have hpA:¬IsUnit (p:A) := by
    intro h
    exact hp (by simpa only [map_natCast] using h.map (algebraMap A B))
  have hp0A:(p:A)≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
  have hnb:differentIdeal A B≠⊥ := by
    intro hz
    exact (LenstraDifferent318.different_not_le_degree_mul A K B L (p:A) hp0A hpA) (by rw [hz]; exact bot_le)
  have hgen:generator (differentIdeal A B)≠0 := by
    intro hz
    exact hnb ((eq_bot_iff_generator_eq_zero (differentIdeal A B)).mpr hz)
  have hf:addVal B (generator (differentIdeal A B))≠⊤ :=
    fun hz=>hgen ((IsDiscreteValuationRing.addVal_eq_top_iff (R:=B)).mp hz)
  have he:idealOrderIsoENat B (differentIdeal A B)=
      OrderDual.toDual (differentExponent A B:ℕ∞) := by
    exact (ENat.natCast_toNat hf).symm
  calc
    differentIdeal A B = (idealOrderIsoENat B).symm
      ((idealOrderIsoENat B) (differentIdeal A B)) := ((idealOrderIsoENat B).symm_apply_apply _).symm
    _ = (idealOrderIsoENat B).symm (OrderDual.toDual (differentExponent A B:ℕ∞)) := by rw [he]
    _ = IsLocalRing.maximalIdeal B ^ differentExponent A B := rfl

/-- The actual local different bound with no supplied valuation estimate.
The hypothesis p≤d is the branch-prime restriction used by the source. -/
theorem different_exponent_le_two_log (p d:ℕ) [Fact p.Prime]
    (hp:¬IsUnit (p:B)) (hpd:p≤d) (hdegree:Module.finrank K L≤d) :
    differentExponent A B ≤ 2*(addVal B (p:B)).toNat*Nat.log p d := by
  have h:=different_exponent_lt A K B L p hp
  have hv:padicValNat p (Module.finrank K L)≤Nat.log p d :=
    (padicValNat_le_nat_log _).trans (Nat.log_mono_right hdegree)
  have hm:1≤Nat.log p d :=
    Nat.le_log_of_pow_le (Fact.out:p.Prime).one_lt (by simpa using hpd)
  have hn:padicValNat p (Module.finrank K L)+1≤2*Nat.log p d := by omega
  have hb:=Nat.mul_le_mul_left (addVal B (p:B)).toNat hn
  exact le_trans (Nat.le_of_lt h) (by simpa only [mul_assoc,mul_left_comm] using hb)

/-- The exact floor(log d/log p) form consumed by the finite-divisor proof. -/
theorem different_exponent_le_two_floor (p d:ℕ) [Fact p.Prime]
    (hp:¬IsUnit (p:B)) (hpd:p≤d) (hdegree:Module.finrank K L≤d) :
    differentExponent A B ≤
      2*(addVal B (p:B)).toNat*⌊Real.log (d:ℝ)/Real.log (p:ℝ)⌋₊ := by
  rw [← Real.logb,Real.natFloor_logb_natCast]
  exact different_exponent_le_two_log A K B L p d hp hpd hdegree

/-- If the model's ramification factors identify v_B(p)=e·e_p, the exact
source coefficient 2e·e_p·floor(log d/log p) follows from the actual different. -/
theorem ramified_vertical_bound (p d e ep:ℕ) [Fact p.Prime]
    (hp:¬IsUnit (p:B)) (hpd:p≤d) (hdegree:Module.finrank K L≤d)
    (hram:(addVal B (p:B)).toNat=e*ep) :
    differentExponent A B ≤ 2*e*ep*⌊Real.log (d:ℝ)/Real.log (p:ℝ)⌋₊ := by
  simpa only [hram,mul_assoc] using different_exponent_le_two_floor A K B L p d hp hpd hdegree

end LenstraVertical318
