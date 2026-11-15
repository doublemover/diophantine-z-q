module
public import PELOriginalDescendedLabelAction318
public section
noncomputable section
namespace PELOriginalDescendedCharacterKernel318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalKernelStableOpens318
open PELOriginalDescendedLabelMaps318 PELOriginalDescendedLabelAction318

/-- Exact kernel for WHOLE scheme automorphisms: the original analytic
character kernel, not merely a subgroup that fixes closed points. -/
theorem descended_eq_id_iff (i:Fin 4) (a:Labels):
    descended i a=𝟙 (Curve i) ↔ a∈(character i).ker:=by
  constructor
  · intro h
    apply (PELOriginalWholeCharacterDeck318.whole_deck_iff i a).mp
    rw [←descended_square,h,Category.comp_id]
  · intro h
    apply cancel_original i
    rw [descended_square,PELOriginalWholeCharacterDeck318.whole_deck_square i a h,
      Category.comp_id]

/-- Equality of two descended maps is EXACTLY equality of the original
character values. The two original cosets are neither merged nor relabeled. -/
theorem descended_eq_iff (i:Fin 4) (a b:Labels):
    descended i a=descended i b ↔ character i a=character i b:=by
  have hprod:descended i (a*b⁻¹)=𝟙 (Curve i) ↔
      descended i a=descended i b:=by
    rw [descended_mul]
    constructor
    · intro h
      have hh:=congrArg (fun f=>f≫descended i b) h
      have hinv:descended i b⁻¹≫descended i b=𝟙 (Curve i):=by
        rw [←descended_mul,inv_mul_cancel,descended_one]
      simpa only [Category.assoc,hinv,Category.comp_id,Category.id_comp] using hh
    · intro h
      rw [h,←descended_mul,mul_inv_cancel,descended_one]
  rw [←hprod,descended_eq_id_iff]
  change character i (a*b⁻¹)=1 ↔ _
  rw [map_mul,map_inv,mul_inv_eq_one]

@[expose] def residual (i:Fin 4):Curve i≅Curve i:=descendedIso i (toggle i)
lemma residual_nontrivial (i:Fin 4):(residual i).hom≠𝟙 (Curve i):=by
  intro h
  exact toggle_nontrivial i ((descended_eq_id_iff i (toggle i)).mp h)
lemma residual_square (i:Fin 4):(residual i).hom≫(residual i).hom=𝟙 (Curve i):=
  descended_square_id i (toggle i)
lemma descended_two_cases (i:Fin 4) (a:Labels):
    descended i a=𝟙 (Curve i) ∨ descended i a=(residual i).hom:=by
  rcases character_cases i a with h|h
  · exact Or.inl ((descended_eq_id_iff i a).mpr h)
  · exact Or.inr ((descended_eq_iff i a (toggle i)).mpr h)
end PELOriginalDescendedCharacterKernel318
