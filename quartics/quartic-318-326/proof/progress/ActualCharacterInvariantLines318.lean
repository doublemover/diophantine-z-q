module
public import CharacterGlobalDifferentialDescent318
public import CharacterGlobalDifferentialInjective318
public import ActualQuotientConstantPullback318
public section
noncomputable section
namespace ActualCharacterInvariantLines318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CharacterTargetDifferentialInvariants318
open ActualTargetRationalInvariants318 ActualQuotientConstantPullback318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev M:=ContactIntrinsicDifferentials318.omega units
/-- Multiplication uses the original structural rational constants in the
actual source regular-function ring, not a newly chosen rational action. -/
@[expose] def parameter (i:Fin 4) (a:ℚ):Γ(M,⊤):=
  sourceConstant a • ContactCharacterDifferentials318.differential i
lemma pullback_parameter (i:Fin 4) (a:ℚ):
    pullback i (characterConstant i a • ContactCharacterDifferentials318.invariant i)=parameter i a:=
  character_invariant_multiple i a
lemma parameter_injective (i:Fin 4):Function.Injective (parameter i):=by
  intro a b h
  apply (character_bijective i).injective
  apply CharacterGlobalDifferentialInjective318.injective i
  exact (pullback_parameter i a).trans (h.trans (pullback_parameter i b).symm)
/-- Each actual fixing-kernel invariant global differential is uniquely
an original structural rational multiple of its specified source pullback. -/
theorem fixed_iff_existsUnique (i:Fin 4) (s:Γ(M,⊤)):
    CharacterDifferentialInvariants318.Fixed i s ↔ ∃!a:ℚ,parameter i a=s:=by
  constructor
  · intro hs
    obtain ⟨t,ht⟩:=CharacterGlobalDifferentialDescent318.exists_pullback i s hs
    obtain ⟨a,ha⟩:=(character_bijective i).surjective t
    have he:parameter i a=s:=
      (pullback_parameter i a).symm.trans ((congrArg (pullback i) ha).trans ht)
    exact ⟨a,he,fun b hb=>(parameter_injective i) (hb.trans he.symm)⟩
  · rintro ⟨a,ha,_⟩
    rw [←ha,←pullback_parameter]
    exact CharacterTargetDifferentialInvariants318.fixed i _
theorem range_parameter (i:Fin 4):
    Set.range (parameter i)={s:Γ(M,⊤)|CharacterDifferentialInvariants318.Fixed i s}:=by
  ext s
  constructor
  · rintro ⟨a,ha⟩
    exact (fixed_iff_existsUnique i s).mpr ⟨a,ha,fun b hb=>(parameter_injective i) (hb.trans ha.symm)⟩
  · intro hs
    obtain ⟨a,ha,_⟩:=(fixed_iff_existsUnique i s).mp hs
    exact ⟨a,ha⟩
end ActualCharacterInvariantLines318
