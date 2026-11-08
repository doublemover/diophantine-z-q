module
import all FixedCoordinateFrameFunctor318
import all FifthOpenSigns318
import all FifthAffineCharacter318
import all FifthSignRestriction318
import all FifthGlobalCharacters318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`FixedCoordinateFrameFunctor318,`FifthOpenSigns318,`FifthAffineCharacter318,`FifthSignRestriction318,`FifthGlobalCharacters318]
  for name in #[`FixedCoordinateFrameFunctor318.map_frame,`FifthOpenSigns318.sign_t,`FifthOpenSigns318.epsilon_square,`FifthOpenSigns318.sign_full_root,`FifthOpenSigns318.sign_full_inverse,`FifthOpenSigns318.raw_pullback,`FifthAffineCharacter318.glued_form,`FifthAffineCharacter318.actual_form,`FifthSignRestriction318.restrict_action,`FifthGlobalCharacters318.global_of_affine,`FifthGlobalCharacters318.glued_eigenrelation,`FifthGlobalCharacters318.actual_eigenrelation] do
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
  logInfo m!"FIFTH_DIFFERENTIAL_CHARACTER_AUDIT_PASS declarations={checked} modules={found}"
