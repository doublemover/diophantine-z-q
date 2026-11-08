module
import all FiniteDoublingUnit318
import all FiniteDoublingOpenLift318
import all FiniteCompletedEqualizer318
import all LiteralFiniteKernel318
import all LiteralFiniteKernelFiber318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FiniteDoublingUnit318, `FiniteDoublingOpenLift318, `FiniteCompletedEqualizer318, `LiteralFiniteKernel318, `LiteralFiniteKernelFiber318]
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked+1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing module"
  logInfo m!"FINITE_NONVERTICAL_KERNEL_AUDIT_PASS declarations={checked} modules={found}"
