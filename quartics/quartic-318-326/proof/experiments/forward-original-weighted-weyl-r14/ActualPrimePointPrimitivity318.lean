module
public import ActualOriginalResidueRemainder318
public import OriginalPrimeWeightedSieve318
public section
noncomputable section
namespace ActualPrimePointPrimitivity318
open scoped BigOperators
open QuadricCRTAssembly318 ActualPrimitiveResidueMap318 OriginalWeightedSelberg318
open OriginalPrimeWeightedSieve318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- True integral primitivity of the original five coordinates: no prime
annihilates all coordinates of the actual reduction. -/
@[expose] def Primitive (κ : ℤ) (v : Quadric κ) : Prop :=
  ∀ p : ℕ,p.Prime → reduction κ p v≠PrimitiveSieveCRT318.origin (κ : ZMod p)

lemma square_dvd_form (κ : ℤ) (γ : J → ℤ) (j : J) (p : ℕ) (v : Quadric κ)
    (hzero : reduction κ p v=PrimitiveSieveCRT318.origin (κ : ZMod p)) :
    (p:ℤ)^2∣form κ γ j v := by
  have hh := (reduction_eq_origin_iff κ p v).mp hzero
  obtain ⟨a,ha⟩ := hh.1.1
  obtain ⟨b,hb⟩ := hh.1.2
  obtain ⟨w,hw⟩ := hh.2.2
  refine ⟨a^2+b^2+γ j*w^2,?_⟩
  dsimp [form]
  rw [ha,hb,hw]
  ring

/-- Even ONE prime-valued original homogeneous form forces true
primitivity. No primality distribution or chosen-generator convention
is used. This is stronger than primitivity only at sieve primes. -/
theorem prime_form_forces_primitive (κ : ℤ) (γ : J → ℤ) (j : J) (v : Quadric κ)
    (hv : (form κ γ j v).natAbs.Prime) : Primitive κ v := by
  intro p hp hzero
  have hd := square_dvd_form κ γ j p v hzero
  have hn : p^2∣(form κ γ j v).natAbs := by
    have hd' : ((p^2:ℕ):ℤ)∣form κ γ j v := by simpa only [Nat.cast_pow] using hd
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd')
  have hpq : p∣(form κ γ j v).natAbs := (show p∣p^2 from ⟨p,by ring⟩).trans hn
  have he : p=(form κ γ j v).natAbs := (hv.dvd_iff_eq hp.ne_one).mp hpq
  have hle := Nat.le_of_dvd hv.pos hn
  rw [←he] at hle
  have hp2 := hp.two_le
  nlinarith

/-- All actual positive prime points of the existing source are primitive
at EVERY prime, before any sieve modulus or removed prime is chosen. -/
theorem original_prime_point_primitive (κ : ℤ) (γ : J → ℤ) (j₀ : J)
    (N : ℕ) (v : Quadric κ) (hv : PrimePoint κ γ N v) : Primitive κ v :=
  prime_form_forces_primitive κ γ j₀ v (hv j₀).2.1

lemma primitive_at_divisor (κ : ℤ) (v : Quadric κ) (hv : Primitive κ v) (d : ℕ) :
    ActualOriginalResidueRemainder318.PrimitiveAtDivisor κ d v := by
  intro i
  exact hv _ (ActualOriginalResidueRemainder318.prime_prime d i)

end ActualPrimePointPrimitivity318
