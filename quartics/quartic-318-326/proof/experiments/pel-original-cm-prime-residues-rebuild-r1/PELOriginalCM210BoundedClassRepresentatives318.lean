module
public import PELOriginalCM210MinkowskiBound318
public section
noncomputable section
namespace PELOriginalCM210BoundedClassRepresentatives318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210MinkowskiBound318
open scoped nonZeroDivisors
/-- Every actual native class has an actual nonzero integral-ideal
representative of norm at most18. Classification of those ideals is separate. -/
lemma bounded_representative (C:ClassGroup O) :
    ∃I:(Ideal O)⁰,ClassGroup.mk0 I=C ∧ Ideal.absNorm (I:Ideal O)≤18 := by
  obtain ⟨I,hI,hn⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  have hn' : (Ideal.absNorm (I:Ideal O):ℝ)≤bound := hn
  have hlt : (Ideal.absNorm (I:Ideal O):ℝ)<19 := lt_of_le_of_lt hn' bound_lt_nineteen
  have hnNat : Ideal.absNorm (I:Ideal O)<19 := by exact_mod_cast hlt
  exact ⟨I,hI,by omega⟩

end PELOriginalCM210BoundedClassRepresentatives318
