module
public import ContactDifferentialCharacters318
public section
noncomputable section
namespace CharacterTargetDifferentialInvariants318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open IntrinsicDifferentialPullback318 IntrinsicDifferentialFunctor318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev p := ContactIntrinsicDifferentials318.structureMap units
abbrev q (i : Fin 4) := WeierstrassGluing318.structureMap (publishedA i) (publishedB i)
abbrev N (i : Fin 4) := FamilyIntrinsicDifferentials318.omega (q i)

/-- The original canonical pullback of every actual target global intrinsic
 differential along the specified completed character map. -/
@[expose] def pullback (i : Fin 4) :
    Γ(N i, ⊤) →+ Γ(ContactIntrinsicDifferentials318.omega units, ⊤) :=
  globalHom (CompletedCharacterGlobal318.completedMap i) p (q i)
    (CompletedCharacterGlobal318.over_Q i)

/-- Every actual regular target global differential pulls back to a section
 fixed by every original source sign that fixes this entire quotient map. -/
theorem fixed (i : Fin 4) (s : Γ(N i, ⊤)) (b : Fin 4 → Bool)
    (hb : CharacterBooleanAffine318.epsilon i b = 1) :
    ContactDifferentialCharacters318.action b (pullback i s) = pullback i s := by
  let f := ContactGlobalSigns318.map units b
  let g := CompletedCharacterGlobal318.completedMap i
  have hfg : (f ≫ g) ≫ q i = p := by
    rw [Category.assoc, CompletedCharacterGlobal318.over_Q]
    exact ContactDifferentialCharacters318.over_Q b
  change globalSection f p p (ContactDifferentialCharacters318.over_Q b)
    (globalSection g p (q i) (CompletedCharacterGlobal318.over_Q i) s) = _
  rw [← globalSection_comp f g p p (q i) (ContactDifferentialCharacters318.over_Q b)
    (CompletedCharacterGlobal318.over_Q i) hfg]
  exact globalSection_congr (CharacterBooleanGlobal318.positive i b hb) p (q i) hfg
    (CompletedCharacterGlobal318.over_Q i) s

/-- The specified invariant is sent to the previously constructed actual
 differential, with no scalar or alternate normalization. -/
theorem pullback_invariant (i : Fin 4) :
    pullback i (ContactCharacterDifferentials318.invariant i) =
      ContactCharacterDifferentials318.differential i := rfl

end CharacterTargetDifferentialInvariants318
