module
public import SourceContactRamification318
public section
noncomputable section
namespace SourceContactRamificationAll318
open ContactKummerOrder318 Polynomial
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) (i:Fin 4)
local instance contactPrime:(SourceContactPrime318.prime i).IsPrime:=
  (SourceContactPrime318.maximal i).isPrime
local instance sourceFinite:Module.Finite R (SourceOrder c):=(source_finite_free c).1
local instance sourceIntegral:Algebra.IsIntegral R (SourceOrder c):=Algebra.IsIntegral.of_finite R (SourceOrder c)
local instance sourceFaithful:FaithfulSMul R (SourceOrder c):=
  (faithfulSMul_iff_algebraMap_injective R (SourceOrder c)).mpr
    (SourceBranchValuation318.polynomial_injective c)
/-- Every literal finite contact has actual primes above it in the full source. -/
theorem primes_nonempty:Nonempty ((SourceContactPrime318.prime i).primesOver (SourceOrder c)):=inferInstance
/-- The base contact's ramification index is two without any supplied
prime, residue point, or prime-existence assumption. -/
theorem ramificationIdxIn_two:
    Ideal.ramificationIdxIn (SourceContactPrime318.prime i) (SourceOrder c)=2:=by
  obtain ⟨Q⟩:=primes_nonempty c i
  apply SourceContactRamification318.ramificationIdxIn_two c Q.val i
  apply (Ideal.mem_of_liesOver Q.val (SourceContactPrime318.prime i) _).mp
  exact Ideal.subset_span (Set.mem_singleton _)
/-- All actual primes above each of the four rational contacts have the
same proved index two, with the original Q[t] structure. -/
theorem every_prime_index_two
    (Q:(SourceContactPrime318.prime i).primesOver (SourceOrder c)):
    Q.val.ramificationIdx R=2:=by
  apply SourceContactRamification318.ramificationIdx_two c Q.val i
  apply (Ideal.mem_of_liesOver Q.val (SourceContactPrime318.prime i) _).mp
  exact Ideal.subset_span (Set.mem_singleton _)
end SourceContactRamificationAll318
