module
import all ModuleFreeOpenFrames318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`ModuleFreeOpenFrames318]
  for name in #[`ModuleFreeOpenFrames318.overFrame,`ModuleFreeOpenFrames318.data,`ModuleFreeOpenFrames318.frame_generators_iso,`ModuleFreeOpenFrames318.data_free,`ModuleFreeOpenFrames318.locallyFree] do
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
  unless found == 1 do throwError "Expected one module, found {found}"
  logInfo m!"MODULE_FREE_OPEN_FRAMES_AUDIT_PASS declarations={checked} modules={found}"
