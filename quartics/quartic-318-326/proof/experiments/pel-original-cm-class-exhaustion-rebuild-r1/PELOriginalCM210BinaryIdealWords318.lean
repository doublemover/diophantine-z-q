module
public import PELOriginalCM210BinaryClassWords318
public import PELOriginalCM210SmallIdealNonprincipal318
public section
noncomputable section
namespace PELOriginalCM210BinaryIdealWords318
open PELOriginalCM210NativeIntegerOrder318 PELOriginalCM210FourNativePrimes318
open PELOriginalCM210NativePrimeClasses318 PELOriginalCM210BinaryClassWords318
open PELOriginalCM210SmallNormObstruction318 PELOriginalCM210SmallIdealNonprincipal318
open scoped nonZeroDivisors
@[expose] def idealBit (i:Fin 4) (a:Bool) : (Ideal O)⁰ :=
  if a then nonzeroIdeal i else 1
@[expose] def wordIdeal (a:Word) : (Ideal O)⁰ :=
  (idealBit 0 a.1*idealBit 1 a.2.1)*idealBit 2 a.2.2
lemma bit_class (i:Fin 4) (a:Bool) : ClassGroup.mk0 (idealBit i a)=bit (primeClass i) a := by
  cases a <;> simp [idealBit,bit,primeClass]
lemma word_class (a:Word) : ClassGroup.mk0 (wordIdeal a)=word a := by
  simp only [wordIdeal,map_mul,bit_class,word]
@[expose] def wordNorm (a:Word) : ℕ :=
  ((if a.1 then 2 else 1)*(if a.2.1 then 3 else 1))*(if a.2.2 then 5 else 1)
lemma word_norm (a:Word) : Ideal.absNorm (wordIdeal a:Ideal O)=wordNorm a := by
  rcases a with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    simp [wordIdeal,idealBit,wordNorm,nonzeroIdeal,map_mul,norm,
      PELPrimeNormalizerData318.prime]
lemma nonzero_norm_data (a:Word) (ha:a≠zero) :
    ∃i:Fin 14,wordNorm a=divisor i := by
  rcases a with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c
  · exact False.elim (ha rfl)
  · exact ⟨2,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨7,rfl⟩
  · exact ⟨0,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨9,rfl⟩
lemma word_nontrivial (a:Word) (ha:a≠zero) : word a≠1 := by
  intro h
  have hp : (wordIdeal a:Ideal O).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (wordIdeal a).property).mp (by simpa only [word_class] using h)
  obtain ⟨i,hi⟩ := nonzero_norm_data a ha
  have hn : Ideal.absNorm (wordIdeal a:Ideal O)=divisor i := (word_norm a).trans hi
  exact no_principal_of_norm _ _ hn
    (by exact_mod_cast (divisor_properties i).2.1) (divisor_nonsquare i) hp
end PELOriginalCM210BinaryIdealWords318
