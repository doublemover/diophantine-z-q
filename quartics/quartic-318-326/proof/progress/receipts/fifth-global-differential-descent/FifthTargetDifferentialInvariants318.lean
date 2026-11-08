module
public import FifthDifferentialInvariantSummand318
public section
noncomputable section
namespace FifthTargetDifferentialInvariants318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open IntrinsicDifferentialPullback318 IntrinsicDifferentialFunctor318
open FifthCharacterShortPolynomial318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev p:=ContactIntrinsicDifferentials318.structureMap units
abbrev q:=WeierstrassGluing318.structureMap A B
abbrev N:=FamilyIntrinsicDifferentials318.omega q
@[expose] def pullback:Γ(N,⊤)→+Γ(ContactIntrinsicDifferentials318.omega units,⊤):=
  globalHom FifthCompletedGlobal318.map p q FifthCompletedGlobal318.over_Q
/-- Every actual regular target global differential pulls back to an
actual global invariant under all eight whole-map-fixing source signs. -/
theorem fixed (s:Γ(N,⊤)):FifthDifferentialInvariantSummand318.Fixed (pullback s):=by
  intro b hb
  let f:=ContactGlobalSigns318.map units b
  let g:=FifthCompletedGlobal318.map
  have hfg:(f≫g)≫q=p:=by
    rw [Category.assoc,FifthCompletedGlobal318.over_Q]
    exact ContactDifferentialCharacters318.over_Q b
  change globalSection f p p (ContactDifferentialCharacters318.over_Q b)
    (globalSection g p q FifthCompletedGlobal318.over_Q s)=_
  rw [←globalSection_comp f g p p q (ContactDifferentialCharacters318.over_Q b)
    FifthCompletedGlobal318.over_Q hfg]
  exact globalSection_congr ((FifthFixingSigns318.mem_iff_fixed b).mp hb) p q hfg
    FifthCompletedGlobal318.over_Q s
end FifthTargetDifferentialInvariants318
