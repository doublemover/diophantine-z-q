module
import all ContactUnbranchedDifferentialFrame318
import all ContactCharacterDifferentialNonzero318
import all ComplementCharacterIndependence318
import all ContactCharacterFrameValues318
import all ContactCharacterFiniteIndependence318
import all ContactCharacterGlobalIndependence318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`ContactUnbranchedDifferentialFrame318,`ContactCharacterDifferentialNonzero318,`ComplementCharacterIndependence318,`ContactCharacterFrameValues318,`ContactCharacterFiniteIndependence318,`ContactCharacterGlobalIndependence318]
  for name in #[`ContactUnbranchedDifferentialFrame318.frame_D,`ContactUnbranchedDifferentialFrame318.D_t_ne_zero,`ContactCharacterDifferentialNonzero318.global_ne_zero,`ComplementCharacterIndependence318.inverse_roots_independent,`ContactCharacterFrameValues318.embedding_z,`ContactCharacterFrameValues318.raw_formula,`ContactCharacterFiniteIndependence318.finite_linear_independent,`ContactCharacterGlobalIndependence318.global_linear_independent] do
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
  logInfo m!"CHARACTER_DIFFERENTIAL_INDEPENDENCE_AUDIT_PASS declarations={checked} modules={found}"
