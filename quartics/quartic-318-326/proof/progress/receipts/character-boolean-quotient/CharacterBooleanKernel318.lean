module
public import CharacterBooleanGlobal318
public import ContactGlobalSignFaithful318
public section
noncomputable section
namespace CharacterBooleanKernel318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterGlobal318 CompletedCharacterInfinity318
open CharacterBooleanAffine318 CharacterBooleanGlobal318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
/-- This equivalence enumerates the actual original field automorphisms,
not arbitrary automorphisms of the projective source. -/
@[expose] def rawSignEquiv:(Fin 4→Bool)≃(L≃ₐ[RatFunc ℚ]L):=
  Equiv.ofBijective sigma ⟨FourRootAutomorphisms318.signEquiv_injective _,by
    intro e
    let a:=SourceKummerField318.parameter units
    obtain ⟨b,hb⟩:=FourRootGalois318.signAutomorphism_surjective a
      ((AlgEquiv.autCongr (KummerTensorField318.rawEquiv a)) e)
    refine ⟨b,?_⟩
    apply (AlgEquiv.autCongr (KummerTensorField318.rawEquiv a)).injective
    exact hb⟩
lemma field_mem_iff (i:Fin 4) (b:Fin 4→Bool):
    sigma b∈(SourceCharacterFields318.field units i).fixingSubgroup↔epsilon i b=1:=by
  rw [sigma,SourceCharacterFields318.sign_mem_fixing_iff]
  change CharacterRoot318.sign (F:=RatFunc ℚ) (SourceCharacterFields318.complement i) b=1↔epsilon i b=1
  constructor
  · intro h
    apply (algebraMap ℚ L).injective
    rw [←epsilon_field,h]
    simp only [map_one]
  · intro h
    apply (algebraMap (RatFunc ℚ) L).injective
    rw [epsilon_field,h]
    simp only [map_one]
/-- The precise positive Boolean kernel is the already specified actual
character-field fixing subgroup, with its actual automorphisms. -/
@[expose] def positiveEquiv (i:Fin 4):{b:Fin 4→Bool // epsilon i b=1}≃
    (SourceCharacterFields318.field units i).fixingSubgroup:=
  rawSignEquiv.subtypeEquiv (fun b=>(field_mem_iff i b).symm)
lemma positive_card (i:Fin 4):Nat.card {b:Fin 4→Bool // epsilon i b=1}=8:=by
  rw [Nat.card_congr (positiveEquiv i)]
  exact SourceCharacterFields318.fixing_subgroup_card units i
@[expose] def stabilizerEquiv (i:Fin 4):
    {b:Fin 4→Bool // ContactGlobalSigns318.map units b≫completedMap i=completedMap i}≃
      (SourceCharacterFields318.field units i).fixingSubgroup:=
  (Equiv.subtypeEquivRight (fixes_iff i)).trans (positiveEquiv i)
/-- Exactly eight original sign patterns stabilize the entire actual quotient
map, matching the already proved function-field degree eight. -/
theorem stabilizer_card (i:Fin 4):
    Nat.card {b:Fin 4→Bool // ContactGlobalSigns318.map units b≫completedMap i=completedMap i}=8:=by
  rw [Nat.card_congr (stabilizerEquiv i)]
  exact SourceCharacterFields318.fixing_subgroup_card units i
/-- This is a count of eight distinct actual whole-Scheme maps, not merely
an eight-element indexing set with possible repetitions. -/
theorem stabilizer_image_card (i:Fin 4):Nat.card (Set.range
    (fun b:{b:Fin 4→Bool // ContactGlobalSigns318.map units b≫completedMap i=completedMap i}=>
      ContactGlobalSigns318.map units b.val))=8:=by
  have hi:Function.Injective
      (fun b:{b:Fin 4→Bool // ContactGlobalSigns318.map units b≫completedMap i=completedMap i}=>
        ContactGlobalSigns318.map units b.val):=by
    intro b d h
    exact Subtype.ext (ContactGlobalSignFaithful318.injective units h)
  rw [←Nat.card_congr (Equiv.ofInjective _ hi)]
  exact stabilizer_card i
end CharacterBooleanKernel318
