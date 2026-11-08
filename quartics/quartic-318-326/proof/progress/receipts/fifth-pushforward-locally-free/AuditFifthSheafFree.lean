module
import all PushforwardStructureSheaf318
import all AffineSpecFreePushforward318
import all ModuleFrameTransport318
import all AffinePushforwardFrame318
import all FifthPushforwardModule318
import all FifthPushforwardLocallyFree318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`PushforwardStructureSheaf318,`AffineSpecFreePushforward318,`ModuleFrameTransport318,`AffinePushforwardFrame318,`FifthPushforwardModule318,`FifthPushforwardLocallyFree318]
  for name in #[`PushforwardStructureSheaf318.object,`PushforwardStructureSheaf318.scalar,`PushforwardStructureSheaf318.restriction,`PushforwardStructureSheaf318.sections,`AffineSpecFreePushforward318.globalsEquiv,`AffineSpecFreePushforward318.fromTilde_isIso,`AffineSpecFreePushforward318.iso,`AffineSpecFreePushforward318.iso_hom_inv,`AffineSpecFreePushforward318.iso_inv_hom,`ModuleFrameTransport318.alongIso,`ModuleFrameTransport318.fromSpec,`AffinePushforwardFrame318.specFrame,`AffinePushforwardFrame318.frame,`AffinePushforwardFrame318.frame_hom_inv,`AffinePushforwardFrame318.frame_inv_hom,`FifthPushforwardModule318.pullback,`FifthPushforwardModule318.trace,`FifthPushforwardModule318.pullback_component,`FifthPushforwardModule318.trace_component,`FifthPushforwardModule318.pullback_trace,`FifthPushforwardLocallyFree318.openAt,`FifthPushforwardLocallyFree318.covers,`FifthPushforwardLocallyFree318.frame,`FifthPushforwardLocallyFree318.frame_hom_inv,`FifthPushforwardLocallyFree318.frame_inv_hom,`FifthPushforwardLocallyFree318.data,`FifthPushforwardLocallyFree318.data_free,`FifthPushforwardLocallyFree318.generator_index,`FifthPushforwardLocallyFree318.locallyFree] do
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
  unless found == 6 do throwError "Expected six modules, found {found}"
  logInfo m!"FIFTH_SHEAF_FREE_AUDIT_PASS declarations={checked} modules={found}"
