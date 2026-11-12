module
public import PELLevelThreeSimilitudes318
public section
noncomputable section
namespace PELPrimeNormalizerData318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELQuaternionDivision318
set_option maxHeartbeats 1200000
@[expose] def prime : Fin 4 → ℕ := ![2,3,5,7]
@[expose] def coefficients : Fin 4 → Coordinates :=
  ![![-6,-2,-4,3],![-6,-2,-3,3],![-2,0,-1,0],![-7,-5,-7,7]]
@[expose] def element (i : Fin 4) : B := embed (coefficients i)

theorem prime_coverage (p : ℕ) : (∃ i,prime i=p) ↔ p=2 ∨ p=3 ∨ p=5 ∨ p=7 := by
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> norm_num [prime]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

theorem prime_ne_zero (i : Fin 4) : (prime i:ℚ)≠0 := by fin_cases i <;> norm_num [prime]
theorem prime_positive (i : Fin 4) : 0<(prime i:ℚ) := by fin_cases i <;> norm_num [prime]
theorem element_mem (i : Fin 4) : element i∈order := ⟨coefficients i,rfl⟩

theorem element_norm (i : Fin 4) : reducedNorm (element i)=prime i := by
  fin_cases i <;> norm_num [element,coefficients,prime,embed,reducedNorm]

theorem element_ne_zero (i : Fin 4) : element i≠0 := by
  intro h
  have hn := element_norm i
  rw [h] at hn
  have hz : reducedNorm (0:B)=0 := by norm_num [reducedNorm]
  rw [hz] at hn
  exact prime_ne_zero i hn.symm

/-- These are actual units of the rational quaternion algebra, not units of
its integral order (their norms are the four ramified-prime candidates). -/
@[expose] def rationalUnit (i : Fin 4) : Bˣ :=
  ⟨element i,reciprocal (element i),mul_reciprocal _ (element_ne_zero i),
    reciprocal_mul _ (element_ne_zero i)⟩

theorem rationalUnit_value (i : Fin 4) : (rationalUnit i:B)=element i := rfl

theorem rationalUnit_inverse (i : Fin 4) : ((rationalUnit i)⁻¹:Bˣ).val=
    (prime i:ℚ)⁻¹ • star (element i) := by
  change reciprocal (element i)=_
  rw [reciprocal,element_norm]
end PELPrimeNormalizerData318
