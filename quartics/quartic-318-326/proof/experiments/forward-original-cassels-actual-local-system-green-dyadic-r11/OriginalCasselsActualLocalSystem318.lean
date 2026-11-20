module
public import OriginalCasselsRealLocalCokernel318
public import OriginalCasselsNaturalPrimeValuation318
public import OriginalCasselsTernaryLocalCokernel318
public import OriginalCasselsRamifiedLocalCokernel318
public import OriginalCasselsGoodLocalCokernel318
import all OriginalSelectedCasselsParity318
public section

noncomputable section

namespace OriginalCasselsActualLocalSystem318

open OriginalSelectedCasselsParity318 OriginalCasselsRealLocalCokernel318
open OriginalCasselsLiteralRangeFinite318 OriginalCasselsOddLocalFinite318
open OriginalCasselsNaturalPrimeValuation318 OriginalCasselsTernaryLocalCokernel318
open OriginalCasselsOddUnitSquare318 OriginalCasselsRamifiedLocalCokernel318
open OriginalCasselsGoodLocalCokernel318

local instance : DecidableEq ℝ := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- One actual system of the same literal signed point map at every
place. Only the local proof of finiteness differs at two and odd p. -/
def actualLocalSystem (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) : LocalSystem n hn where
  real := localRealIsogeny (n:ℝ) (Nat.cast_ne_zero.mpr hn.ne')
  padic := fun p hp =>
    letI : Fact p.Prime := ⟨hp⟩
    if he : p=2 then
      by
        subst p
        exact localDyadicIsogeny n hn hr
    else
      localOddIsogeny he (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne')

private theorem actual_cokernel_at_two (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    (actualLocalSystem n hn hr).finiteCokernelCard 2 Nat.prime_two=2 := by
  unfold LocalSystem.finiteCokernelCard actualLocalSystem
  split
  · exact local_dyadic_cokernel_card n hn hr
  · rename_i he
    exact (he (by decide)).elim

private theorem actual_cokernel_at_odd (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11)
    (p : ℕ) (hp : p.Prime) (hp2 : p≠2) : letI : Fact p.Prime := ⟨hp⟩
      (actualLocalSystem n hn hr).finiteCokernelCard p hp =
        (localOddIsogeny hp2 (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne')).cokernelCard := by
  dsimp only [LocalSystem.finiteCokernelCard,actualLocalSystem]
  rw [dif_neg hp2]

/-- The five exact local rows on the same actual isogeny system, including
every good prime. No epsilon factors or global Cassels/Selmer formula. -/
theorem actualExactLocalCokernels (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) : ExactLocalCokernels (actualLocalSystem n hn hr) := by
  refine ⟨?_, actual_cokernel_at_two n hn hr, ?_, ?_, ?_⟩
  · change (localRealIsogeny (n:ℝ) (Nat.cast_ne_zero.mpr hn.ne')).cokernelCard=1
    exact actual_real_cokernel_card _ _
  · rw [actual_cokernel_at_odd n hn hr 3 Nat.prime_three (by decide)]
    exact local_ternary_cokernel_card n hn hr
  · intro p hm hp
    obtain ⟨hp2,hp3⟩ := selected_primeFactors_ne_two_three hn hr hm
    have hp5 := five_le_prime_of_ne_two_three hp hp2 hp3
    letI : Fact p.Prime := ⟨hp⟩
    have hv := selected_ramified_four_n_valuation n p hn hs hp5 hm
    have hmod : (p:ZMod 3)=1 ↔ p%3=1 :=
      ZMod.natCast_eq_natCast_iff' p 1 3
    rw [actual_cokernel_at_odd n hn hr p hp hp2,
      actual_ramified_cokernel_card hp5 hp2 (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne') hv,hmod]
  · intro p hp hp2 hp3 hm
    have hp5 := five_le_prime_of_ne_two_three hp hp2 hp3
    letI : Fact p.Prime := ⟨hp⟩
    have hD : ¬p∣n := fun hd => hm ((Nat.mem_primeFactors_of_ne_zero hn.ne').mpr ⟨hp,hd⟩)
    have hNZ : (n:ZMod p)≠0 := fun hz => hD ((ZMod.natCast_eq_zero_iff n p).mp hz)
    have hU : IsUnit (n:ℤ_[p]) :=
      (residue_nonzero_iff_unit _).mp (by simpa only [map_natCast] using hNZ)
    rw [actual_cokernel_at_odd n hn hr p hp hp2]
    simpa only [PadicInt.coe_natCast] using actual_good_cokernel_card hp5 hp2 (n:ℤ_[p]) hU

end OriginalCasselsActualLocalSystem318

#print axioms OriginalCasselsActualLocalSystem318.actualLocalSystem
#print axioms OriginalCasselsActualLocalSystem318.actualExactLocalCokernels
