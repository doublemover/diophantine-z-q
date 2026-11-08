module
public import ContactGlobalDifferentialCoefficient318
public import CharacterBooleanKernel318
public section
noncomputable section
namespace CharacterDifferentialInvariants318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open ContactGlobalDifferentialCoefficient318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev M:=ContactIntrinsicDifferentials318.omega units
abbrev G:=Γ(M,⊤)
local instance rawField:Field L:=(KummerTensorField318.source_raw_field units).toField
/-- Invariance under the exact eight original source signs fixing the entire
specified complementary quotient map, not a point-stabilizer condition. -/
@[expose] def Fixed (i:Fin 4) (s:G):Prop:=∀b,CharacterBooleanAffine318.epsilon i b=1→
  ContactDifferentialCharacters318.action b s=s
lemma fixed_iff_maps (i:Fin 4) (s:G):Fixed i s ↔ ∀b,
    ContactGlobalSigns318.map units b≫CompletedCharacterGlobal318.completedMap i=
      CompletedCharacterGlobal318.completedMap i→ContactDifferentialCharacters318.action b s=s:=by
  simp only [Fixed,CharacterBooleanGlobal318.fixes_iff]
lemma own_fixed (i:Fin 4):Fixed i (ContactCharacterDifferentials318.differential i):=
  fun b hb=>ContactDifferentialCharacters318.positive i b hb
lemma omitted_flip_positive (i:Fin 4):CharacterBooleanAffine318.epsilon i (SourceCharacterFields318.flip i)=1:=
  (CharacterBooleanKernel318.field_mem_iff i _).mp (SourceCharacterFields318.omitted_flip_fixes units i)
lemma omitted_fixed (i:Fin 4) (s:G) (h:Fixed i s):
    ContactDifferentialCharacters318.action (SourceCharacterFields318.flip i) s=s:=
  h _ (omitted_flip_positive i)
/-- Actual invariance puts the literal dt coefficient in the specified
original character subfield. This makes no claim of target regularity. -/
theorem coefficient_mem (i:Fin 4) (s:G) (h:Fixed i s):
    coefficient s∈SourceCharacterFields318.field units i:=by
  rw [←SourceCharacterFields318.actual_fixed_field units i,IntermediateField.mem_fixedField_iff]
  intro σ hσ
  obtain ⟨b,hb⟩:=(CharacterBooleanKernel318.positiveEquiv i).surjective ⟨σ,hσ⟩
  have he:CharacterBooleanAffine318.sigma b.val=σ:=congrArg Subtype.val hb
  rw [←he]
  change FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b.val (coefficient s)=_
  rw [←coefficient_action,h b.val b.property]
end CharacterDifferentialInvariants318
