module
import all FifthSourceInfinityCoordinates318
import all FifthSourceInfinityAlgebra318
import all FifthSourceInfinityScheme318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`FifthSourceInfinityCoordinates318,`FifthSourceInfinityAlgebra318,`FifthSourceInfinityScheme318]
  for name in #[`FifthSourceInfinityCoordinates318.u_embedding,`FifthSourceInfinityCoordinates318.v_embedding,`FifthSourceInfinityCoordinates318.x_embedding,`FifthSourceInfinityCoordinates318.y_embedding,`FifthSourceInfinityAlgebra318.shortMap,`FifthSourceInfinityAlgebra318.original_field_square,`FifthSourceInfinityScheme318.over_Q,`FifthSourceInfinityScheme318.generic_square] do
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
  unless found == 3 do throwError "Expected three modules, found {found}"
  logInfo m!"FIFTH_SOURCE_INFINITY_AUDIT_PASS declarations={checked} modules={found}"
