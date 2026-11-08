module
import all InfinityOutputZero318
import all FiniteLocalZero318
import all FiniteZeroScheme318
import all FiniteAdditionZero318
import all FiniteAdditionZeroFiber318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`InfinityOutputZero318, `FiniteLocalZero318, `FiniteZeroScheme318, `FiniteAdditionZero318, `FiniteAdditionZeroFiber318]
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
  logInfo m!"FINITE_ZERO_CONVERSE_AUDIT_PASS declarations={checked} modules={found}"
