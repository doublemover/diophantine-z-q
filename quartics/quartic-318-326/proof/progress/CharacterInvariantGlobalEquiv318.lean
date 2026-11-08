module
public import CharacterGlobalDifferentialInjective318
public import CharacterGlobalDifferentialDescent318
public section
noncomputable section
namespace CharacterInvariantGlobalEquiv318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CharacterTargetDifferentialInvariants318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev M:=ContactIntrinsicDifferentials318.omega units
/-- The actual additive subgroup of whole global source sections fixed by
all eight source signs fixing the specified whole quotient map. -/
@[expose] def invariants (i:Fin 4):AddSubgroup Γ(M,⊤) where
  carrier:={s|CharacterDifferentialInvariants318.Fixed i s}
  zero_mem':=by intro b hb;exact map_zero (ContactDifferentialCharacters318.action b)
  add_mem':=by
    intro s t hs ht b hb
    rw [map_add,hs b hb,ht b hb]
  neg_mem':=by
    intro s hs b hb
    rw [map_neg,hs b hb]
@[expose] def intoInvariants (i:Fin 4):Γ(N i,⊤)→+invariants i where
  toFun s:=⟨pullback i s,CharacterTargetDifferentialInvariants318.fixed i s⟩
  map_zero':=by apply Subtype.ext;exact map_zero (pullback i)
  map_add':=by intro s t;apply Subtype.ext;exact map_add (pullback i) s t
lemma bijective (i:Fin 4):Function.Bijective (intoInvariants i):=by
  constructor
  · intro s t h
    exact CharacterGlobalDifferentialInjective318.injective i (congrArg Subtype.val h)
  · intro s
    obtain ⟨t,ht⟩:=CharacterGlobalDifferentialDescent318.exists_pullback i s.val s.property
    exact ⟨t,Subtype.ext ht⟩
/-- Original regular target global Omega is additively equivalent to its
actual invariant global source subgroup by the canonical pullback. -/
@[expose] def equiv (i:Fin 4):Γ(N i,⊤)≃+invariants i:=
  AddEquiv.ofBijective (intoInvariants i) (bijective i)
lemma equiv_val (i:Fin 4) (s:Γ(N i,⊤)):(equiv i s).val=pullback i s:=rfl
lemma inverse_pullback (i:Fin 4) (s:Γ(N i,⊤)):
    (equiv i).symm (intoInvariants i s)=s:=(equiv i).symm_apply_apply s
lemma pullback_inverse (i:Fin 4) (s:invariants i):
    pullback i ((equiv i).symm s)=s.val:=congrArg Subtype.val ((equiv i).apply_symm_apply s)
lemma invariant_normalization (i:Fin 4):
    (equiv i (ContactCharacterDifferentials318.invariant i)).val=
      ContactCharacterDifferentials318.differential i:=rfl
end CharacterInvariantGlobalEquiv318
