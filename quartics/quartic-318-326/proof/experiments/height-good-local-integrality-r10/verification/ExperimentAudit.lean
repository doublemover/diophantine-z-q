module
import all IntegralCotangentTensor318
import all VerticalCotangentSections318
import all ReducedVerticalUniformizer318
import all ReducedVerticalTensorSections318
import all KilledUniformizerSections318
import all ReducedBaseTensorSections318
import all LocalizedReducedFiber318
import all LocalizedBaseTensorSections318
import all IntegralContactOpenFrame318
import all EtaleFlatReduced318
import all IntegralContactReduced318
import all EtaleQuotientReduced318
import all IntegralContactWholeFiber318
import all IntegralContactLocalSections318
import all EtaleHeightOneLocal318
import all IntegralContactVerticalDVR318
import all IntegralContactActualVertical318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`IntegralCotangentTensor318,`VerticalCotangentSections318,`ReducedVerticalUniformizer318,`ReducedVerticalTensorSections318,`KilledUniformizerSections318,`ReducedBaseTensorSections318,`LocalizedReducedFiber318,`LocalizedBaseTensorSections318,`IntegralContactOpenFrame318,`EtaleFlatReduced318,`IntegralContactReduced318,`EtaleQuotientReduced318,`IntegralContactWholeFiber318,`IntegralContactLocalSections318,`EtaleHeightOneLocal318,`IntegralContactVerticalDVR318,`IntegralContactActualVertical318]
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
