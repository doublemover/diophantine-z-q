module
import all CompletedCharacterLineNormHom318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`CompletedCharacterLineNormHom318]
  for n in #[`CompletedCharacterLineNormHom318.norm_unit,`CompletedCharacterLineNormHom318.norm_product,
      `CompletedCharacterLineNormHom318.norm,`CompletedCharacterLineNormHom318.on_representatives,
      `CompletedCharacterLineNormHom318.maps_inverse,`CompletedCharacterLineNormHom318.maps_power] do
    unless env.contains n do throwError "Required endpoint missing: {n}"
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
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing target module"
  logInfo m!"CHARACTER_NORM_HOM_AUDIT_PASS declarations={count} modules={found}"
