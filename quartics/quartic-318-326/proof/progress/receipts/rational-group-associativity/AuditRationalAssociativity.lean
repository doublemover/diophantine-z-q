module
import all RationalWeierstrassPoints318
import all RationalCompletedPoints318
import all RationalChordPoints318
import all RationalTangentPoints318
import all RationalInfinityPoints318
import all RationalFiniteAdditionPoints318
import all RationalCompletedAdditionPoints318
import all RationalAssociativityTest318
import all RationalProductReduced318
import all RationalGroupAssociativity318
import Lean.Util.CollectAxioms
-- Exceptional j-values remain covered: no hidden nonzero-A/nonzero-B premise.
example : CompletedAdditionTriple318.leftAssociate (0:ℚ) 1 (by norm_num)=
    CompletedAdditionTriple318.rightAssociate (0:ℚ) 1 (by norm_num):=
  RationalGroupAssociativity318.associative 0 1 (by norm_num)
example : CompletedAdditionTriple318.leftAssociate (1:ℚ) 0 (by norm_num)=
    CompletedAdditionTriple318.rightAssociate (1:ℚ) 0 (by norm_num):=
  RationalGroupAssociativity318.associative 1 0 (by norm_num)
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`RationalWeierstrassPoints318,`RationalCompletedPoints318,`RationalChordPoints318,`RationalTangentPoints318,`RationalInfinityPoints318,`RationalFiniteAdditionPoints318,`RationalCompletedAdditionPoints318,`RationalAssociativityTest318,`RationalProductReduced318,`RationalGroupAssociativity318]
  for name in #[`RationalWeierstrassPoints318.fieldPointEquiv,`RationalCompletedPoints318.fieldPointEquiv,`RationalChordPoints318.chord_add,`RationalTangentPoints318.tangent_add,`RationalInfinityPoints318.zero_denominator_add,`RationalFiniteAdditionPoints318.actual_add,`RationalCompletedAdditionPoints318.actual_add,`RationalAssociativityTest318.field_test,`RationalProductReduced318.triple_reduced,`RationalGroupAssociativity318.associative] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        checked := checked+1
  unless found == 10 do throwError "Expected ten modules, found {found}"
  logInfo m!"RATIONAL_GROUP_ASSOCIATIVITY_AUDIT_PASS declarations={checked} modules={found}"
