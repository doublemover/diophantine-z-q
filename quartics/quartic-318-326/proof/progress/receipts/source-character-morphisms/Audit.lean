module
import all SourceCharacterAlgebra318
import all SourceCharacterAffine318
import all SourceCharacterGlobal318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`SourceCharacterAlgebra318,`SourceCharacterAffine318,`SourceCharacterGlobal318]
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if wanted.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == wanted.size do throwError "Missing modules"
  logInfo m!"SOURCE_CHARACTER_GLOBAL_AUDIT_PASS declarations={checked} modules={found}"
