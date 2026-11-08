module
public import BranchDifferentialDivisibility318
public import CharacterDifferentialInvariants318
public import ContactBranchRepresentation318
public section
noncomputable section
namespace BranchGlobalDifferentialRestriction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev X:=ContactBranchRepresentation318.X units
abbrev B (i:Fin 4):=ContactBranchRepresentation318.B units i
abbrev j (i:Fin 4):=ContactBranchRepresentation318.j units i
abbrev p:=ContactBranchRepresentation318.p units
abbrev M:=ContactBranchRepresentation318.M units
@[expose] def form (i:Fin 4):=ContactBranchRepresentation318.representation units i
@[expose] def form_restrict (i:Fin 4) (s:Γ(M,⊤)):=
  ContactBranchRepresentation318.representation_restrict units i s
/-- Canonical global pullback through the actual whole branch/sign square. -/
@[expose] def form_action (i:Fin 4) (s:Γ(M,⊤)):=
  ContactBranchRepresentation318.representation_action units i (SourceCharacterFields318.flip i)
    (ContactDifferentialCharacters318.over_Q (SourceCharacterFields318.flip i)) s
/-- Every actual complementary-kernel invariant has a regular y_i dy_i
factor on its entire omitted branch. -/
theorem invariant_factorization (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s):
    ∃a:B i,form i s=(ContactFrameNormalization318.sourceCoordinate units i*a) •
      KaehlerDifferential.D ℚ (B i) (ContactFrameNormalization318.sourceCoordinate units i):=by
  apply BranchDifferentialDivisibility318.fixed_factorization
  exact (form_action i s).symm.trans
    (congrArg (form i) (CharacterDifferentialInvariants318.omitted_fixed i s h))
end BranchGlobalDifferentialRestriction318
