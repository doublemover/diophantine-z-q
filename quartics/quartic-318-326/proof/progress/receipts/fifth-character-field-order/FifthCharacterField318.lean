module
public import FifthCharacterPolynomial318
public section
noncomputable section
namespace FifthCharacterField318
open Polynomial SourceTwistArithmetic318 KummerTensorField318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev K := RatFunc ℚ
abbrev L := Raw (SourceKummerField318.parameter units)
@[expose] def support : Finset (Fin 4) := Finset.univ
instance radicandNonsquare : Fact (¬IsSquare
    (CharacterRoot318.radicand (SourceKummerField318.parameter units) support)) :=
  ⟨SourceKummerField318.product_nonsquare units _ (by exact ⟨0,Finset.mem_univ _⟩)⟩
@[expose] def field : IntermediateField K L :=
  CharacterQuadraticField318.field (SourceKummerField318.parameter units) support
@[expose] def root : L := CharacterRoot318.root (SourceKummerField318.parameter units) support

theorem radicand_quartic :
    CharacterRoot318.radicand (SourceKummerField318.parameter units) support =
      algebraMap ℚ[X] K FifthCharacterPolynomial318.quartic := by
  rw [←FifthCharacterPolynomial318.full_product]
  simp only [CharacterRoot318.radicand,support,SourceKummerField318.parameter,
    ContactKummerOrder318.coefficient,map_prod,map_mul,map_sub,map_C,map_X]

theorem root_square : root^2 = algebraMap K L
    (algebraMap ℚ[X] K FifthCharacterPolynomial318.quartic) :=
  (CharacterRoot318.root_square _ _).trans (congrArg (algebraMap K L) radicand_quartic)

theorem field_eq_adjoin : field = IntermediateField.adjoin K {root} :=
  CharacterQuadraticField318.field_eq_adjoin _ _
theorem degree_two : Module.finrank K field=2 := CharacterQuadraticField318.degree_two _ _
theorem relative_degree_eight : Module.finrank field L=8 :=
  CharacterQuadraticField318.relative_degree_eight _ _
theorem actual_fixed_field : IntermediateField.fixedField field.fixingSubgroup=field :=
  CharacterQuadraticField318.actual_fixed_field _ _
theorem sign_mem_fixing_iff (b:Fin 4→Bool) :
    FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b∈field.fixingSubgroup ↔
      (∏ j:Fin 4,(if b j then (-1:K) else 1))=1 :=
  CharacterQuadraticField318.sign_mem_fixing_iff _ _ _
theorem fixing_subgroup_card : Nat.card field.fixingSubgroup=8 :=
  CharacterQuadraticField318.fixing_subgroup_card _ _
end FifthCharacterField318
