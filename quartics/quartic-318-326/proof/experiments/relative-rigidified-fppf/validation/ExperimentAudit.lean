module
import all TensorPullbackCocycle318
import all LineClassPullbackHom318
import all RelativeLineClassQuotient318
import all RelativeLineClassBaseChange318
import all RelativeLineSectionNormalization318
import all RelativeRigidifiedLine318
import all RelativeSectionBaseChange318
import all RelativeSectionNaturality318
import all RelativeLineFunctorPullback318
import all RelativeFppfLineSheaf318
import all RelativeFppfLineLocal318
import all RelativeFppfRigidifiedLocal318
import all RelativeFppfLineNeutral318
import all FourRootPointTorsor318
import all RationalFourRootFiber318
import all RationalContactPoint318
import all ContactFieldSection318
import all ContactFieldRigidification318
import all ContactFppfRigidifiedLocal318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`TensorPullbackCocycle318,`LineClassPullbackHom318,`RelativeLineClassQuotient318,`RelativeLineClassBaseChange318,`RelativeLineSectionNormalization318,`RelativeRigidifiedLine318,`RelativeSectionBaseChange318,`RelativeSectionNaturality318,`RelativeLineFunctorPullback318,`RelativeFppfLineSheaf318,`RelativeFppfLineLocal318,`RelativeFppfRigidifiedLocal318,`RelativeFppfLineNeutral318,`FourRootPointTorsor318,`RationalFourRootFiber318,`RationalContactPoint318,`ContactFieldSection318,`ContactFieldRigidification318,`ContactFppfRigidifiedLocal318]
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        count := count+1
  unless found == modules.size do throwError "Missing imported modules: {found}/{modules.size}"
  logInfo m!"EXPERIMENT_AUDIT_PASS declarations={count} modules={found}"
