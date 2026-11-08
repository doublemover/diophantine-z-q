module
public import FifthGlobalDifferentialInjective318
public import FifthGlobalDifferentialDescent318
public section
noncomputable section
namespace FifthInvariantGlobalEquiv318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthTargetDifferentialInvariants318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev M:=ContactIntrinsicDifferentials318.omega units
abbrev I:=FifthDifferentialInvariantSummand318.invariants
/-- The original canonical global pullback, with its actual invariant
codomain property retained rather than an abstractly chosen additive map. -/
@[expose] def intoInvariants:Γ(N,⊤)→+I where
  toFun s:=⟨pullback s,fixed s⟩
  map_zero':=by apply Subtype.ext;exact map_zero pullback
  map_add':=by intro s t;apply Subtype.ext;exact map_add pullback s t
lemma bijective:Function.Bijective intoInvariants:=by
  constructor
  · intro s t h
    exact FifthGlobalDifferentialInjective318.injective (congrArg Subtype.val h)
  · intro s
    obtain ⟨t,ht⟩:=FifthGlobalDifferentialDescent318.exists_pullback s.val s.property
    exact ⟨t,Subtype.ext ht⟩
/-- Actual regular target global differentials and the original eight-sign
invariant source global summand are additively equivalent, by the original
pullback and its unique inverse. No dimension or Picard identification is used. -/
@[expose] def equiv:Γ(N,⊤)≃+I:=AddEquiv.ofBijective intoInvariants bijective
lemma equiv_val (s:Γ(N,⊤)):(equiv s).val=pullback s:=rfl
/-- The normalized averaging map descends to actual regular target global
Omega through the inverse of the original injective pullback. -/
@[expose] def retraction:Γ(M,⊤)→+Γ(N,⊤):=
  equiv.symm.toAddMonoidHom.comp FifthDifferentialInvariantSummand318.retraction
lemma pullback_retraction (s:Γ(M,⊤)):
    pullback (retraction s)=FifthDifferentialAveraging318.average s:=by
  have h:=congrArg Subtype.val (equiv.apply_symm_apply
    (FifthDifferentialInvariantSummand318.retraction s))
  exact h
lemma retraction_pullback (s:Γ(N,⊤)):retraction (pullback s)=s:=by
  apply FifthGlobalDifferentialInjective318.injective
  rw [pullback_retraction]
  exact FifthDifferentialInvariantSummand318.average_eq_of_fixed _ (fixed s)
/-- The fifth actual pulled invariant returns to its specified original
elliptic invariant, with scalar one. -/
lemma retraction_fifth:retraction FifthActualDifferential318.differential=
    FifthActualDifferential318.invariant:=retraction_pullback _
/-- Each of the four other actual elliptic pullbacks vanishes under this
normalized transfer on regular global differentials. -/
lemma retraction_complementary (i:Fin 4):
    retraction (ContactCharacterDifferentials318.differential i)=0:=by
  apply FifthGlobalDifferentialInjective318.injective
  rw [pullback_retraction,map_zero]
  exact FifthDifferentialAveraging318.average_complementary i
end FifthInvariantGlobalEquiv318
