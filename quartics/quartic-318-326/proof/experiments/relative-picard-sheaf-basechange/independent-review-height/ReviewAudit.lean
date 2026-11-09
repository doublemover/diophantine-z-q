module
import all TensorPullbackCocycle318
import all LineClassPullbackHom318
import all RelativeLineClassQuotient318
import all RelativeLineClassBaseChange318
import all RelativeLineBaseChangeIso318
import all RelativeLineFunctorPullback318
import all RelativeFppfLineSheaf318
import all RelativeFppfBaseChangeIso318
import all FourRootPointTorsor318
import all RationalFourRootFiber318
import all RationalContactPoint318
import all ContactFieldSection318
import all ContactRelativeLinePresheaf318
import all RelativeFppfLineLocal318
import all ContactFppfLineSheaf318
import all ContactFppfFieldBaseChange318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`TensorPullbackCocycle318,`LineClassPullbackHom318,`RelativeLineClassQuotient318,`RelativeLineClassBaseChange318,`RelativeLineBaseChangeIso318,`RelativeLineFunctorPullback318,`RelativeFppfLineSheaf318,`RelativeFppfBaseChangeIso318,`FourRootPointTorsor318,`RationalFourRootFiber318,`RationalContactPoint318,`ContactFieldSection318,`ContactRelativeLinePresheaf318,`RelativeFppfLineLocal318,`ContactFppfLineSheaf318,`ContactFppfFieldBaseChange318]
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
  logInfo m!"INDEPENDENT_BASECHANGE_AUDIT_PASS declarations={count} modules={found}"
