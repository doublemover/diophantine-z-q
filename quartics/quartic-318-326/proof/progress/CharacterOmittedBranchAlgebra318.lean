module
public import BranchGlobalDifferentialRestriction318
public import RegularUnitMultiple318
public import CharacterBranchVectorFactorization318
public section
noncomputable section
namespace CharacterOmittedBranchAlgebra318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open BranchGlobalDifferentialRestriction318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
/-- Whole-ring coordinate divisibility and the specified normalized local
coefficient produce a regular multiple, retaining the exact inferred objects. -/
@[expose] def form_multiple (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s) :=
  (invariant_factorization i s h).elim (fun a ha=>
    RegularUnitMultiple318.of_factorizations
      (ContactFrameNormalization318.sourceCoordinate units i) a
      (CharacterBranchLocalForm318.unitCoefficient i i)
      (form i s) (CharacterBranchLocalForm318.form i i)
      (KaehlerDifferential.D ℚ (B i) (ContactFrameNormalization318.sourceCoordinate units i))
      (CharacterBranchLocalForm318.unitCoefficient_unit i i) ha
      (CharacterBranchVectorFactorization318.factorization i))
run_cmd do
  let out ← IO.getStdout
  out.putStrLn "DONE form_multiple"
  out.flush
end CharacterOmittedBranchAlgebra318
