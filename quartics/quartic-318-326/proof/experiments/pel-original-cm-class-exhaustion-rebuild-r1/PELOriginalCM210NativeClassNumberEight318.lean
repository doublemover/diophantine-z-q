module
public import PELOriginalCM210BinaryIdealWords318
public section
noncomputable section
namespace PELOriginalCM210NativeClassNumberEight318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210BinaryClassWords318 PELOriginalCM210BinaryIdealWords318
lemma xor_eq_zero_iff (x y:Word) : xor x y=zero ↔ x=y := by
  rcases x with ⟨a,b,c⟩
  rcases y with ⟨d,e,f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    decide
lemma word_injective : Function.Injective word := by
  intro a b h
  have hxor : word (xor a b)=1 := by rw [←word_mul,h,word_square]
  have hz : xor a b=zero := by
    by_contra hn
    exact word_nontrivial _ hn hxor
  exact (xor_eq_zero_iff a b).mp hz
/-- A produced bijection with all native ideal classes of the original field. -/
@[expose] def classEquiv : Word≃ClassGroup O :=
  Equiv.ofBijective word ⟨word_injective,word_surjective⟩
lemma classEquiv_formula (a:Word) : classEquiv a=word a := rfl
lemma native_cardinality : Nat.card (ClassGroup O)=8 := by
  rw [←Nat.card_congr classEquiv,Nat.card_eq_fintype_card]
  decide
lemma class_number : NumberField.classNumber K=8 := by
  simpa only [NumberField.classNumber,Nat.card_eq_fintype_card] using native_cardinality
end PELOriginalCM210NativeClassNumberEight318
