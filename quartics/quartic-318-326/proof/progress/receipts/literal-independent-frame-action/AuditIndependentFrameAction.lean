module
import all F3FrameChange318
import all LiteralKernelPointBaseTransport318
import all LiteralKernelFrameChange318
import all LiteralIndependentFrameChange318
import all LiteralIndependentFrameAction318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`F3FrameChange318,`LiteralKernelPointBaseTransport318,`LiteralKernelFrameChange318,`LiteralIndependentFrameChange318,`LiteralIndependentFrameAction318]
  for name in #[`F3FrameChange318.change_mul,`F3FrameChange318.change_natural,`F3FrameChange318.independent,`LiteralKernelPointBaseTransport318.pull_val,`LiteralKernelFrameChange318.map_base,`LiteralKernelFrameChange318.map_mul,`LiteralKernelFrameChange318.iso,`LiteralIndependentFrameChange318.preserves,`LiteralIndependentFrameChange318.map_inclusion,`LiteralIndependentFrameChange318.map_mul,`LiteralIndependentFrameChange318.iso,`LiteralIndependentFrameAction318.action_mul,`LiteralIndependentFrameAction318.natural,`LiteralIndependentFrameAction318.action_first,`LiteralIndependentFrameAction318.action_second] do
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
  unless found == 5 do throwError "Expected five modules, found {found}"
  logInfo m!"INDEPENDENT_FRAME_ACTION_AUDIT_PASS declarations={checked} modules={found}"
