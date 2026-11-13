module
public import PELOriginalCM210SmallPrimePowers318
public import PELOriginalCM210PrimeResidueExclusions318
public section
noncomputable section
namespace PELOriginalCM210BoundedMaximalIdeals318
open PELOriginalCM210NativeIntegerOrder318 PELOriginalCM210FourNativePrimes318
open PELOriginalCM210SmallPrimePowers318 PELOriginalCM210MaximalTheta318
open PELOriginalCM210PrimeResidueExclusions318
/-- Classification in the actual full ring of integers, with literal kernel equality. -/
lemma classify (P:Ideal O) [P.IsMaximal] (h:Ideal.absNorm P≤18) :
    ∃i:Fin 4,P=ideal i := by
  obtain ⟨p,n,hn,hpP,hp,hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  have hpow : p^n≤18 := hnorm ▸ h
  have hp18 : p≤18 := le_trans (base_le_power p n hp.pos hn) hpow
  rcases small_prime p hp hp18 with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨0,prime_over_ramified P 0 (by simpa [PELPrimeNormalizerData318.prime] using hpP)⟩
  · exact ⟨1,prime_over_ramified P 1 (by simpa [PELPrimeNormalizerData318.prime] using hpP)⟩
  · exact ⟨2,prime_over_ramified P 2 (by simpa [PELPrimeNormalizerData318.prime] using hpP)⟩
  · exact ⟨3,prime_over_ramified P 3 (by simpa [PELPrimeNormalizerData318.prime] using hpP)⟩
  · have he := large_exponent_one 11 n (by omega) hn hpow
    exact False.elim ((norm_excluded P).1 (by simpa [he] using hnorm))
  · have he := large_exponent_one 13 n (by omega) hn hpow
    exact False.elim ((norm_excluded P).2.1 (by simpa [he] using hnorm))
  · have he := large_exponent_one 17 n (by omega) hn hpow
    exact False.elim ((norm_excluded P).2.2 (by simpa [he] using hnorm))
end PELOriginalCM210BoundedMaximalIdeals318
