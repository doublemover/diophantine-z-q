module
public import PELOriginalCM210MaximalTheta318
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public section
noncomputable section
namespace PELOriginalCM210PrimeResidueExclusions318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210MaximalTheta318
lemma no_root_eleven (x:ZMod 11) : x^2≠(-210:ZMod 11) := by
  revert x
  decide
lemma no_root_thirteen (x:ZMod 13) : x^2≠(-210:ZMod 13) := by
  revert x
  decide
lemma no_root_seventeen (x:ZMod 17) : x^2≠(-210:ZMod 17) := by
  revert x
  decide
lemma residue_root (P:Ideal O) [P.IsMaximal] (p:ℕ) (hp:p.Prime)
    (h:Ideal.absNorm P=p) : ∃x:ZMod p,x^2=(-210:ZMod p) := by
  have hP : P≠⊥ := by
    intro hzero
    rw [hzero,Ideal.absNorm_bot] at h
    exact hp.ne_zero h.symm
  letI : Ring.HasFiniteQuotients O := Ring.HasFiniteQuotients.of_module_finite ℤ O
  letI : Finite (O⧸P) := Ring.HasFiniteQuotients.finiteQuotient hP
  letI : Fintype (O⧸P) := Fintype.ofFinite _
  have hc : Fintype.card (O⧸P)=p := by
    simpa only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using h
  let e := ZMod.ringEquivOfPrime (O⧸P) hp hc
  refine ⟨e.symm (Ideal.Quotient.mk P theta),?_⟩
  have he := congrArg (fun z:O=>e.symm (Ideal.Quotient.mk P z)) theta_square
  simpa using he
lemma norm_excluded (P:Ideal O) [P.IsMaximal] :
    Ideal.absNorm P≠11 ∧ Ideal.absNorm P≠13 ∧ Ideal.absNorm P≠17 := by
  refine ⟨?_,?_,?_⟩
  · intro h
    obtain ⟨x,hx⟩ := residue_root P 11 (by norm_num) h
    exact no_root_eleven x hx
  · intro h
    obtain ⟨x,hx⟩ := residue_root P 13 (by norm_num) h
    exact no_root_thirteen x hx
  · intro h
    obtain ⟨x,hx⟩ := residue_root P 17 (by norm_num) h
    exact no_root_seventeen x hx
end PELOriginalCM210PrimeResidueExclusions318
