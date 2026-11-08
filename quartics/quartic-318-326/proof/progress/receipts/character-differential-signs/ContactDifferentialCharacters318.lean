module
public import PublishedInvariantNegation318
public import IntrinsicDifferentialFunctor318
public import ContactCharacterGlobalIndependence318
public section
noncomputable section
namespace ContactDifferentialCharacters318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open IntrinsicDifferentialPullback318 IntrinsicDifferentialFunctor318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

lemma over_Q (b:Fin 4→Bool):
    ContactGlobalSigns318.map units b≫ContactIntrinsicDifferentials318.structureMap units=
      ContactIntrinsicDifferentials318.structureMap units:=by
  change ContactGlobalSigns318.map units b≫ContactProjectiveModel318.modelMap units≫
    ProjectiveJLine318.structureMap ℚ=_
  rw [←Category.assoc,ContactGlobalSigns318.over_line]
  rfl

/-- Canonical pullback by the actual entire source-sign Scheme automorphism. -/
@[expose] def action (b:Fin 4→Bool):
    Γ(ContactIntrinsicDifferentials318.omega units,⊤)→+
      Γ(ContactIntrinsicDifferentials318.omega units,⊤):=
  globalHom (ContactGlobalSigns318.map units b) (ContactIntrinsicDifferentials318.structureMap units)
    (ContactIntrinsicDifferentials318.structureMap units) (over_Q b)

theorem positive (i:Fin 4) (b:Fin 4→Bool) (he:CharacterBooleanAffine318.epsilon i b=1):
    action b (ContactCharacterDifferentials318.differential i)=
      ContactCharacterDifferentials318.differential i:=by
  let p:=ContactIntrinsicDifferentials318.structureMap units
  let q:=WeierstrassGluing318.structureMap (publishedA i) (publishedB i)
  let f:=ContactGlobalSigns318.map units b
  let g:=CompletedCharacterGlobal318.completedMap i
  have hfg:(f≫g)≫q=p:=by
    rw [Category.assoc,CompletedCharacterGlobal318.over_Q]
    exact over_Q b
  change globalSection f p p (over_Q b)
    (globalSection g p q (CompletedCharacterGlobal318.over_Q i)
      (ContactCharacterDifferentials318.invariant i))=_
  rw [←globalSection_comp f g p p q (over_Q b) (CompletedCharacterGlobal318.over_Q i) hfg]
  exact globalSection_congr (CharacterBooleanGlobal318.positive i b he) p q hfg
    (CompletedCharacterGlobal318.over_Q i) (ContactCharacterDifferentials318.invariant i)

theorem negative (i:Fin 4) (b:Fin 4→Bool) (he:CharacterBooleanAffine318.epsilon i b=-1):
    action b (ContactCharacterDifferentials318.differential i)=
      -ContactCharacterDifferentials318.differential i:=by
  let p:=ContactIntrinsicDifferentials318.structureMap units
  let q:=WeierstrassGluing318.structureMap (publishedA i) (publishedB i)
  let f:=ContactGlobalSigns318.map units b
  let g:=CompletedCharacterGlobal318.completedMap i
  let n:=GluedNegation318.negation (publishedA i) (publishedB i)
  have hfg:(f≫g)≫q=p:=by
    rw [Category.assoc,CompletedCharacterGlobal318.over_Q]
    exact over_Q b
  have hgn:(g≫n)≫q=p:=by
    rw [Category.assoc,GluedNegation318.negation_over_base]
    exact CompletedCharacterGlobal318.over_Q i
  change globalSection f p p (over_Q b)
    (globalSection g p q (CompletedCharacterGlobal318.over_Q i)
      (ContactCharacterDifferentials318.invariant i))=_
  rw [←globalSection_comp f g p p q (over_Q b) (CompletedCharacterGlobal318.over_Q i) hfg]
  rw [globalSection_congr (CharacterBooleanGlobal318.negative i b he) p q hfg hgn]
  rw [globalSection_comp g n p q q (CompletedCharacterGlobal318.over_Q i)
    (GluedNegation318.negation_over_base (publishedA i) (publishedB i)) hgn,
    PublishedInvariantNegation318.invariant_negation,globalSection_neg]
  rfl

/-- All sixteen source signs act on each actual global differential by the
literal complementary triple-root character, with exact scalar one. -/
theorem eigenrelation (i:Fin 4) (b:Fin 4→Bool):
    action b (ContactCharacterDifferentials318.differential i)=
      ContactCharacterGlobalIndependence318.constants (CharacterBooleanAffine318.epsilon i b) •
        ContactCharacterDifferentials318.differential i:=by
  rcases CharacterBooleanAffine318.epsilon_values i b with he|he
  · rw [positive i b he,he,map_one,one_smul]
  · rw [negative i b he,he,map_neg,map_one,neg_one_smul]
end ContactDifferentialCharacters318
