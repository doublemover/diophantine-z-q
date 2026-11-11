module
public import PELOriginalRamifiedSquare318
public section
noncomputable section
namespace PELOriginalRamifiedDivision318
open PELPrincipalOrderCoordinates318 PELPrimeNormalizerData318 PELPrimeRightLattice318
open PELOriginalRamifiedResidues318 PELOriginalRamifiedKernels318 PELPrimeLatticeResidues318
open PELLevelThreeSimilitudes318 PELQuaternionAlgebra318
set_option maxHeartbeats 1800000

theorem norm_reduction (i : Fin 4) (a : Coordinates) :
    QuadraticAlgebra.norm (reduceCoordinates i a)=(integralNorm a:ZMod (prime i)) := by
  fin_cases i <;>
    simp [reduceCoordinates,QuadraticAlgebra.norm_def,integralNorm,quadraticA,quadraticB,prime] <;>
    push_cast <;> norm_num <;> ring

/-- Actual divisibility in the original quaternion order follows from the
FIELD residue norm, not just congruence of a chosen determinant. -/
theorem prime_div_norm_iff (i : Fin 4) (a : Coordinates) :
    (prime i:ℤ)∣integralNorm a ↔ ∃ b : Coordinates,product b (coefficients i)=a := by
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd (integralNorm a) (prime i),←norm_reduction,
    QuadraticAlgebra.norm_eq_zero_iff_eq_zero,reduction_zero_iff,←residue_zero_iff,kernel_iff]

@[expose] def orderNorm (x : order) : ℤ := integralNorm (coordinatesEquiv.symm x)
@[expose] def uniformizer (i : Fin 4) : order := coordinatesEquiv (coefficients i)

theorem orderNorm_value (x : order) : reducedNorm (x:B)=(orderNorm x:ℚ) := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  simpa only [orderNorm,AddEquiv.symm_apply_apply] using original_norm a

theorem orderNorm_mul (x y : order) : orderNorm (x*y)=orderNorm x*orderNorm y := by
  have h := PELQuaternionNormParity318.norm_mul (x:B) (y:B)
  change reducedNorm ((x*y:order):B)=_ at h
  rw [orderNorm_value,orderNorm_value,orderNorm_value] at h
  exact_mod_cast h

theorem orderNorm_one : orderNorm 1=1 := by
  have h := orderNorm_value (1:order)
  norm_num [reducedNorm] at h
  exact_mod_cast h.symm

theorem orderNorm_pow (x : order) (k : ℕ) : orderNorm (x^k)=orderNorm x^k := by
  induction k with
  | zero => simpa only [pow_zero] using orderNorm_one
  | succ k ih => rw [pow_succ,orderNorm_mul,ih,pow_succ]

theorem uniformizer_norm (i : Fin 4) : orderNorm (uniformizer i)=(prime i:ℤ) := by
  have h := element_norm i
  change reducedNorm ((uniformizer i:order):B)=(prime i:ℚ) at h
  rw [orderNorm_value] at h
  exact_mod_cast h

theorem actual_prime_division (i : Fin 4) (x : order) :
    (prime i:ℤ)∣orderNorm x ↔ ∃ y : order,y*uniformizer i=x := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  change (prime i:ℤ)∣integralNorm a ↔ _
  rw [prime_div_norm_iff]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨coordinatesEquiv b,?_⟩
    change coordinatesEquiv b*coordinatesEquiv (coefficients i)=coordinatesEquiv a
    rw [←PELOrderReductionThree318.coordinates_mul,hb]
  · rintro ⟨b,hb⟩
    obtain ⟨c,rfl⟩ := coordinatesEquiv.surjective b
    change coordinatesEquiv c*coordinatesEquiv (coefficients i)=coordinatesEquiv a at hb
    rw [←PELOrderReductionThree318.coordinates_mul] at hb
    exact ⟨c,coordinatesEquiv.injective hb⟩

/-- Every original norm valuation depth is realized by division by the SAME
prime normalizer power inO. This is a local arithmetic/optimal-embedding input;
it does not identify integral conjugacy classes or analytic branch orbits. -/
theorem actual_prime_power_division (i : Fin 4) (k : ℕ) (x : order) :
    (prime i:ℤ)^k∣orderNorm x ↔ ∃ y : order,y*(uniformizer i)^k=x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hp : (prime i:ℤ)≠0 := by exact_mod_cast (NeZero.ne (prime i))
    constructor
    · intro h
      have hpdiv : (prime i:ℤ)∣orderNorm x := by
        have hh : (prime i:ℤ)∣(prime i:ℤ)^(k+1) := by
          refine ⟨(prime i:ℤ)^k,?_⟩
          rw [pow_succ] <;> ring
        exact hh.trans h
      obtain ⟨z,hz⟩ := (actual_prime_division i x).mp hpdiv
      have hzdiv : (prime i:ℤ)^k∣orderNorm z := by
        rw [←hz,orderNorm_mul,uniformizer_norm,pow_succ] at h
        obtain ⟨r,hr⟩ := h
        refine ⟨r,?_⟩
        apply mul_right_cancel₀ hp
        calc
          orderNorm z*(prime i:ℤ)=((prime i:ℤ)^k*(prime i:ℤ))*r := hr
          _ = ((prime i:ℤ)^k*r)*(prime i:ℤ) := by ring
      obtain ⟨y,hy⟩ := (ih z).mp hzdiv
      refine ⟨y,?_⟩
      rw [pow_succ,←mul_assoc,hy,hz]
    · rintro ⟨y,rfl⟩
      rw [orderNorm_mul,orderNorm_pow,uniformizer_norm]
      exact ⟨orderNorm y,mul_comm _ _⟩
end PELOriginalRamifiedDivision318
