module
public import PELOriginalCM210NativeClassGeneration318
public section
noncomputable section
namespace PELOriginalCM210BinaryClassWords318
open PELOriginalCM210NativeIntegerOrder318 PELOriginalCM210NativePrimeClasses318
open PELOriginalCM210NativeClassProductRelation318
abbrev Word := Bool×Bool×Bool
@[expose] def bit (g:ClassGroup O) (a:Bool) : ClassGroup O := if a then g else 1
@[expose] def word (a:Word) : ClassGroup O :=
  (bit (primeClass 0) a.1*bit (primeClass 1) a.2.1)*bit (primeClass 2) a.2.2
@[expose] def zero : Word := (false,false,false)
@[expose] def xor (a b:Word) : Word :=
  (Bool.xor a.1 b.1,Bool.xor a.2.1 b.2.1,Bool.xor a.2.2 b.2.2)
lemma bit_mul (i:Fin 4) (a b:Bool) :
    bit (primeClass i) a*bit (primeClass i) b=bit (primeClass i) (Bool.xor a b) := by
  have hs : primeClass i*primeClass i=1 := by simpa only [pow_two] using class_square i
  cases a <;> cases b <;> simp [bit,hs]
lemma word_mul (a b:Word) : word a*word b=word (xor a b) := by
  unfold word
  calc
    _ = ((bit (primeClass 0) a.1*bit (primeClass 0) b.1)*
      (bit (primeClass 1) a.2.1*bit (primeClass 1) b.2.1))*
      (bit (primeClass 2) a.2.2*bit (primeClass 2) b.2.2) := by abel
    _ = _ := by simp only [bit_mul,xor]
lemma word_zero : word zero=1 := by simp [word,zero,bit]
lemma xor_self (a:Word) : xor a a=zero := by
  rcases a with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> rfl
lemma word_square (a:Word) : word a*word a=1 := by rw [word_mul,xor_self,word_zero]
lemma word_inverse (a:Word) : (word a)⁻¹=word a :=
  inv_eq_of_mul_eq_one_right (word_square a)
@[expose] def wordSubgroup : Subgroup (ClassGroup O) where
  carrier := Set.range word
  one_mem' := ⟨zero,word_zero⟩
  mul_mem' := by
    rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨xor a b,(word_mul a b).symm⟩
  inv_mem' := by
    rintro _ ⟨a,rfl⟩
    exact ⟨a,(word_inverse a).symm⟩
lemma primes_mem (i:Fin 4) : primeClass i∈wordSubgroup := by
  fin_cases i
  · exact ⟨(true,false,false),by simp [word,bit]⟩
  · exact ⟨(false,true,false),by simp [word,bit]⟩
  · exact ⟨(false,false,true),by simp [word,bit]⟩
  · exact ⟨(true,true,true),by simpa [word,bit] using fourth_class.symm⟩
lemma word_surjective : Function.Surjective word := by
  intro C
  exact PELOriginalCM210NativeClassGeneration318.every_class_mem wordSubgroup primes_mem C
end PELOriginalCM210BinaryClassWords318
