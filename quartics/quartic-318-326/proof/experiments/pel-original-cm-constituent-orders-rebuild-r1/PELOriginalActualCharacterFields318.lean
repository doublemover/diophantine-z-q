module
public import FourRootActualCharacterFields318
public import PELOriginalContactCharacterIdentity318
public import PELOriginalCommonContactBase318
public section
noncomputable section
namespace PELOriginalActualCharacterFields318
open PELOriginalCommonContactBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
open FourRootActualGenericField318
local instance independentFact:Fact (QuadraticTower318.Independent (parameter branches)):=
  ⟨independent branches branches_injective⟩
@[expose] def omitted (i:Fin 4):Finset (Fin 4):=Finset.univ.erase i
lemma omitted_nonempty (i:Fin 4):(omitted i).Nonempty:=by
  fin_cases i <;> decide
lemma omitted_eq (i:Fin 4):omitted i=
    {SourceTwistArithmetic318.complement i 0,SourceTwistArithmetic318.complement i 1,
      SourceTwistArithmetic318.complement i 2}:=by
  fin_cases i <;> decide
lemma complementary_product (i:Fin 4) (g:FourBinaryCharacters318.Group):
    (∏k∈omitted i,FourBinaryCharacters318.coordinate (F:=ℂ) k g)=
      FourBinaryCharacters318.complementary (F:=ℂ) i g:=by
  rw [omitted_eq]
  fin_cases i <;> simp [FourBinaryCharacters318.complementary,
    SourceTwistArithmetic318.complement,Fin.prod_univ_succ] <;> ring

/-- Actual quadratic subfields inside the full generic field of the SAME
independent contact scheme, with the original omitted-character order. -/
@[expose] def field (i:Fin 4):IntermediateField K (KummerTensorField318.Raw (parameter branches)):=
  FourRootActualCharacterFields318.field branches branches_injective (omitted i) (omitted_nonempty i)

/-- The preimage of the genuine algebraic fixing subgroup is EXACTLY the
original analytic prime-character kernel, on ALL16 original labels. -/
theorem original_kernel (i:Fin 4) (g:Labels):
    FourRootActualGenericSigns318.genericAutomorphism branches (basis g)∈(field i).fixingSubgroup ↔
      g∈(character i).ker:=by
  rw [FourRootActualCharacterFields318.original_sign_mem_fixing_iff,complementary_product]
  exact (PELOriginalContactCharacterIdentity318.field_kernel_iff (F:=ℂ) i g).symm

theorem actual_fixed_field (i:Fin 4):IntermediateField.fixedField (field i).fixingSubgroup=field i:=
  FourRootActualCharacterFields318.actual_fixed_field branches branches_injective _ _
theorem degree_two (i:Fin 4):Module.finrank K (field i)=2:=
  FourRootActualCharacterFields318.degree_two branches branches_injective _ _
theorem fixing_subgroup_card (i:Fin 4):Nat.card (field i).fixingSubgroup=8:=
  FourRootActualCharacterFields318.fixing_subgroup_card branches branches_injective _ _

theorem literal_monomial_generator (i:Fin 4):field i=
    IntermediateField.adjoin K
      {affineEmbedding branches (FourRootActualCharacterFields318.monomial branches (omitted i))}:=
  FourRootActualCharacterFields318.field_eq_actual_adjoin branches branches_injective _ _
end PELOriginalActualCharacterFields318
