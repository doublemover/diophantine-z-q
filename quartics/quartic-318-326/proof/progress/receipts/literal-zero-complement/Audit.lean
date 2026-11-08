module
import all CompletedZeroTripling318
import all LiteralKernelZeroSection318
import all InfinityOriginNeighborhood318
import all LiteralComplementNeighborhood318
import all LiteralKernelComplementZero318
import all LiteralFullKernel318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`CompletedZeroTripling318, `LiteralKernelZeroSection318, `InfinityOriginNeighborhood318, `LiteralComplementNeighborhood318, `LiteralKernelComplementZero318, `LiteralFullKernel318]
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
  logInfo m!"FULL_KERNEL_AUDIT_PASS declarations={checked} modules={found}"
