module
public import ActualPrimePointPrimitivity318
public section
noncomputable section
namespace ActualPrimitiveSourceRestriction318
open scoped BigOperators
open QuadricCRTAssembly318 ActualPrimePointPrimitivity318 OriginalPrimeWeightedSieve318
open OriginalWeightedSelberg318 ActualOriginalResidueRemainder318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The original finite source restricted to true global primitivity.
It is chosen without reference to N, a removed prime, or any divisor. -/
@[expose] def primitiveSource (κ : ℤ) (S : Finset (Quadric κ)) : Finset (Quadric κ) := by
  classical
  exact S.filter (Primitive κ)
lemma mem_primitiveSource (κ : ℤ) (S : Finset (Quadric κ)) (v : Quadric κ) :
    v∈primitiveSource κ S ↔ v∈S ∧ Primitive κ v := by
  classical
  exact Finset.mem_filter

/-- True primitivity loses NONE of the original positive prime points,
and keeps exactly their original logarithmic weights. -/
theorem original_prime_mass_preserved (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N : ℕ)
    (S : Finset (Quadric κ)) :
    primeWeightedSum κ γ N (primitiveSource κ S)=primeWeightedSum κ γ N S := by
  classical
  unfold primeWeightedSum primitiveSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : PrimePoint κ γ N v
  · rw [if_pos (original_prime_point_primitive κ γ j₀ N v hv),if_pos hv]
  · simp only [hv,ite_false,ite_self]

/-- Every later divisor restriction is automatically satisfied on the
already chosen global primitive source. There is no d-dependent source
substitution or loss of a target prime point. -/
lemma original_primitive_filter_eq (κ : ℤ) (S : Finset (Quadric κ)) (d : ℕ) :
    (primitiveSource κ S).filter (PrimitiveAtDivisor κ d)=primitiveSource κ S := by
  classical
  apply Finset.filter_eq_self.mpr
  intro v hv
  exact primitive_at_divisor κ v (mem_primitiveSource κ S v |>.mp hv).2 d
lemma original_imprimitive_filter_empty (κ : ℤ) (S : Finset (Quadric κ)) (d : ℕ) :
    (primitiveSource κ S).filter (fun v => ¬PrimitiveAtDivisor κ d v)=∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro v hv hnot
  exact hnot (primitive_at_divisor κ v (mem_primitiveSource κ S v |>.mp hv).2 d)

/-- Actual imprimitive mass is exactly zero on this source, not merely
an assumed negligible error. This is valid for every d simultaneously. -/
theorem original_imprimitive_mass_zero (κ : ℤ) (γ : J → ℤ)
    (S : Finset (Quadric κ)) (d : ℕ) :
    (∑v∈(primitiveSource κ S).filter (fun v => ¬PrimitiveAtDivisor κ d v),weight κ γ v)=0 := by
  classical
  rw [original_imprimitive_filter_empty,Finset.sum_empty]

end ActualPrimitiveSourceRestriction318
