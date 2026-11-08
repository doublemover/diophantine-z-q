module
import all LinePullbackFrames318
import all LineSheafPullback318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LinePullbackFrames318, `LineSheafPullback318]
  for name in #[`LinePullbackFrames318.frame, `LinePullbackFrames318.inverse_formula, `LinePullbackFrames318.hom_inv, `LinePullbackFrames318.inv_hom, `LinePullbackFrames318.preimage_cover, `LineSheafPullback318.line, `LineSheafPullback318.congr, `LineSheafPullback318.respects, `LineSheafPullback318.pullback, `LineSheafPullback318.pullback_classOf, `LineSheafPullback318.presentation_independent] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
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
  logInfo m!"ACTUAL_LINE_PULLBACK_AUDIT_PASS declarations={checked} modules={found}"
