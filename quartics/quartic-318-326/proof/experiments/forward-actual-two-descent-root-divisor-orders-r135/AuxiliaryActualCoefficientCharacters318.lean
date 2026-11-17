module
public import AuxiliaryCoefficientResidualUnits318
public import AuxiliaryLocalCharacters318
public import LocalNormPrimeSplitting318
public section
namespace AuxiliaryActualCoefficientCharacters318
open AuxiliaryCoefficientResidualUnits318

private theorem cast_ne (p : ℕ) [Fact p.Prime] (a : ℤ) (h : ¬(p:ℤ)∣a) :
    (a:ZMod p)≠0 := fun hz => h ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)

/-- The two per-prime character identities needed by signed reciprocity
follow from the actual common local values. Residual units, splitting2 at
selected primes and all modular nonzero conditions are derived here.
The finite factorization and its actual local values remain inputs. -/
theorem identities (C ε σ : ℤ) (P U q α : ℕ)
    (hC : C%24=1) (hCs : Squarefree C)
    (hε : ε=1 ∨ ε= -1) (hσ : σ=1 ∨ σ= -1)
    (hfac : C=ε*(P:ℤ)*(U:ℤ)) (hq : q.Prime)
    (hqS : q∉insert 2 (insert 3 C.natAbs.primeFactors))
    (hsix : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣C → IsSquare (6:ZMod p))
    (hA : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣C →
      ∃ X Z : ℚ_[p], X^2-2*Z^2=((σ*2^α*(P:ℤ)*(q:ℤ):ℤ):ℚ_[p]))
    (hB : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣C →
      ∃ T Y : ℚ_[p], (C:ℚ_[p])*T^2-6*Y^2=
        ((σ*2^α*(P:ℤ)*(q:ℤ):ℤ):ℚ_[p])) :
    (∀ p, p.Prime → p∣P →
      jacobiSym (q:ℤ) p=jacobiSym (ε*σ*(U:ℤ)) p) ∧
    (∀ p, p.Prime → p∣U →
      jacobiSym (q:ℤ) p=jacobiSym (-σ*2^α*(P:ℤ)) p) := by
  have hC0 : C≠0 := by intro hz; subst C; norm_num at hC
  constructor
  · intro p hp hpP
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨R,hP,hD,hR,hU⟩ := selected_residuals C ε P U hCs hfac p hp hpP
    have hc : C=(p:ℤ)*(ε*(R:ℤ)*(U:ℤ)) := by rw [hfac,hP]; push_cast; ring
    have hpC : (p:ℤ)∣C := ⟨ε*(R:ℤ)*(U:ℤ),hc⟩
    have h6 := six_unit C hC p hp hpC
    have hq0 := new_prime_unit_of_support C hC0 p q hp hq hpC hqS
    have hRZ : ¬(p:ℤ)∣(R:ℤ) := by exact_mod_cast hR
    have hUZ : ¬(p:ℤ)∣(U:ℤ) := by exact_mod_cast hU
    have htwo : ¬(p:ℤ)∣2 := fun h => h6 (by simpa using dvd_mul_of_dvd_left h (3:ℤ))
    have hp2 : p≠2 := by intro he; subst p; exact htwo (by decide)
    have hσ0 : (σ:ZMod p)≠0 := by rcases hσ with rfl | rfl <;> norm_num
    have hE0 : ((σ*2^α*(R:ℤ)*(q:ℤ):ℤ):ZMod p)≠0 := by
      push_cast
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hσ0
        (pow_ne_zero _ (by simpa using cast_ne p 2 htwo)))
        (cast_ne p R hRZ)) (cast_ne p q hq0)
    have hE : ¬(p:ℤ)∣σ*2^α*(R:ℤ)*(q:ℤ) :=
      fun hd => hE0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd)
    have ht : σ*2^α*(P:ℤ)*(q:ℤ)=(p:ℤ)*(σ*2^α*(R:ℤ)*(q:ℤ)) := by
      rw [hP]; push_cast; ring
    obtain ⟨X,Z,hX⟩ := hA p hpC
    have h2 := LocalNormPrimeSplitting318.jacobi_two_of_local_odd_factor
      p hp2 (σ*2^α*(R:ℤ)*(q:ℤ)) hE Z X
      (hX.trans (congrArg (fun n : ℤ => (n:ℚ_[p])) ht))
    obtain ⟨T,Y,hY⟩ := hB p hpC
    apply AuxiliaryLocalCharacters318.selected_identity p ε σ R U q α
      hε hσ h6 hRZ hUZ hq0 h2 T Y
    simpa only [hc,ht] using hY
  · intro p hp hpU
    letI : Fact p.Prime := ⟨hp⟩
    have hfac' : C=ε*(U:ℤ)*(P:ℤ) := by rw [hfac]; ring
    obtain ⟨R,hU,hD,hR,hP⟩ := selected_residuals C ε U P hCs hfac' p hp hpU
    have hc : C=(p:ℤ)*(ε*(R:ℤ)*(P:ℤ)) := by rw [hfac',hU]; push_cast; ring
    have hpC : (p:ℤ)∣C := ⟨ε*(R:ℤ)*(P:ℤ),hc⟩
    have h6 := six_unit C hC p hp hpC
    have hq0 := new_prime_unit_of_support C hC0 p q hp hq hpC hqS
    have hPZ : ¬(p:ℤ)∣(P:ℤ) := by exact_mod_cast hP
    have htwo : ¬(p:ℤ)∣2 := fun h => h6 (by simpa using dvd_mul_of_dvd_left h (3:ℤ))
    have hσ0 : (σ:ZMod p)≠0 := by rcases hσ with rfl | rfl <;> norm_num
    have hAZ : ((-σ*2^α*(P:ℤ):ℤ):ZMod p)≠0 := by
      push_cast
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hσ0)
        (pow_ne_zero _ (by simpa using cast_ne p 2 htwo))) (cast_ne p P hPZ)
    have hAA : ¬(p:ℤ)∣-σ*2^α*(P:ℤ) :=
      fun hd => hAZ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd)
    have hj6 : jacobiSym 6 p=1 := by
      rw [←jacobiSym.legendreSym.to_jacobiSym p 6]
      exact (legendreSym.eq_one_iff p (by simpa using cast_ne p 6 h6)).mpr (by simpa using hsix p hpC)
    obtain ⟨T,Y,hY⟩ := hB p hpC
    apply AuxiliaryLocalCharacters318.unselected_identity p
      (ε*(R:ℤ)*(P:ℤ)) (-σ*2^α*(P:ℤ)) q h6 hD hAA hq0 hj6 T Y
    have ht : σ*2^α*(P:ℤ)*(q:ℤ)= -(-σ*2^α*(P:ℤ))*(q:ℤ) := by ring
    simpa only [hc,ht] using hY

end AuxiliaryActualCoefficientCharacters318
