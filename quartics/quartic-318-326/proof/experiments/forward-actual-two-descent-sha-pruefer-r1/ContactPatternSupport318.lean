module
public import ContactPrimeFullSource318
public section
noncomputable section
namespace ContactPatternSupport318
open ContactPrimeForms318 ClearedContactForms318 MergedContactPrimePattern318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

@[expose] def row (u w : ℤ) (j : Fin 3) (i : Fin 5) : ℤ := value u w (C.coefficient (j,i))
@[expose] def denominator (w : ℤ) : ℚ := (C.denominator:ℚ)*(w:ℚ)

lemma denominator_ne (w : ℤ) (hw : w≠0) : denominator C w≠0 :=
  mul_ne_zero (by exact_mod_cast Nat.ne_of_gt C.positive) (by exact_mod_cast hw)

lemma scales_eq (j : Fin 3) : ThreeDetectorArithmetic318.scales labels j=scaleRoot labels j := by
  fin_cases j <;> rfl

lemma linear_eq (u w : ℤ) (j : Fin 3) (i : Fin 5) :
    DetectorPrimeProduct318.linear (ThreeDetectorArithmetic318.scales labels j)
      (u:ℚ) (denominator C w) i=(row C u w j i:ℚ) := by
  rw [row,value_exact,scales_eq]
  dsimp [DetectorPrimeProduct318.linear,DetectorPrimeProduct318.theta,root,slope,denominator]
  ring

lemma row_pos (u w : ℤ) (hp : Values C u w) (j : Fin 3) (i : Fin 5) : 0<row C u w j i :=
  (all_positions_prime C u w hp (j,i)).1
lemma row_ne (u w : ℤ) (hp : Values C u w) (j : Fin 3) (i : Fin 5) : row C u w j i≠0 :=
  ne_of_gt (row_pos C u w hp j i)
lemma row_prime (u w : ℤ) (hp : Values C u w) (j : Fin 3) (i : Fin 5) :
    (row C u w j i).natAbs.Prime := (all_positions_prime C u w hp (j,i)).2

/-- Every support prime of a row is one of its actual five selected primes.
The remaining denominator proof therefore needs no infinite family of new
prime hypotheses. Cross-row duplicate positions remain permitted. -/
lemma support_selected (u w : ℤ) (hv : Values C u w) (j : Fin 3) (p : ℕ) (hp : p.Prime)
    (hpos : 0<padicValInt p (DetectorPrimeProduct318.product (row C u w j))) :
    ∃ i : Fin 5, p=(row C u w j i).natAbs := by
  have hd : p∣(DetectorPrimeProduct318.product (row C u w j)).natAbs :=
    padicValNat.dvd_of_ne_zero (by simpa only [padicValInt] using Nat.ne_of_gt hpos)
  simp only [DetectorPrimeProduct318.product,Int.natAbs_mul,hp.dvd_mul] at hd
  rcases hd with h0|h1|h2|h3|h4
  · exact ⟨0,(Nat.prime_dvd_prime_iff_eq hp (row_prime C u w hv j 0)).mp h0⟩
  · exact ⟨1,(Nat.prime_dvd_prime_iff_eq hp (row_prime C u w hv j 1)).mp h1⟩
  · exact ⟨2,(Nat.prime_dvd_prime_iff_eq hp (row_prime C u w hv j 2)).mp h2⟩
  · exact ⟨3,(Nat.prime_dvd_prime_iff_eq hp (row_prime C u w hv j 3)).mp h3⟩
  · exact ⟨4,(Nat.prime_dvd_prime_iff_eq hp (row_prime C u w hv j 4)).mp h4⟩

/-- An actual positive stored pole produces its own quotient domain and
nonzero delta; these are not supplied as extra source-row assumptions. -/
lemma positive_domain (q : ℚ) (h u w : ℤ) (j : Fin 3)
    (hb : 0<ThreeDetectorUniformFamily318.witness q labels h (parameter C u w) (190+51*j.val)) :
    ScaledContactWeights318.delta (ThreeDetectorArithmetic318.scales labels j) (parameter C u w)≠0 ∧
    ScaledDetectorChain318.realChain (DetectorGateWitness318.witness q labels h)
      (ThreeDetectorArithmetic318.scales labels j) (parameter C u w)≠0 := by
  rw [ThreeDetectorArithmetic318.stored_pole] at hb
  constructor
  · intro hz
    simp [ScaledDetectorChain318.poleInput,hz] at hb
  · intro hz
    simp [ScaledDetectorChain318.poleInput,ScaledDetectorChain318.traceQuotient,hz] at hb

end ContactPatternSupport318
