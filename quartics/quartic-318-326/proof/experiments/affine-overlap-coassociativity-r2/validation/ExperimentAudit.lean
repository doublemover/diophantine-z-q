module
import all FaithfullyFlatFinitePresentation318
import all OriginalLineAffineModel318
import all FaithfullyFlatLineModule318
import all AffineRankOneLine318
import all AffineCoalgebraModule318
import all AffineCoalgebraLine318
import all TensorPushoutModule318
import all AffineModuleBaseChange318
import all AffineModuleMate318
import all AffineOverlapCoaction318
import all AffineOverlapDiagonal318
import all ScalarExtensionCongr318
import all ScalarExtensionComposition318
import all AffineCechRings318
import all AffineTripleCoactionCoordinates318
import all AffineTripleOverlapMaps318
import all AffineTripleCoordinateLaws318
import all AffineOverlapCoassociativity318
import all AffineCocycleLine318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`FaithfullyFlatFinitePresentation318,`OriginalLineAffineModel318,`FaithfullyFlatLineModule318,`AffineRankOneLine318,`AffineCoalgebraModule318,`AffineCoalgebraLine318,`TensorPushoutModule318,`AffineModuleBaseChange318,`AffineModuleMate318,`AffineOverlapCoaction318,`AffineOverlapDiagonal318,`ScalarExtensionCongr318,`ScalarExtensionComposition318,`AffineCechRings318,`AffineTripleCoactionCoordinates318,`AffineTripleOverlapMaps318,`AffineTripleCoordinateLaws318,`AffineOverlapCoassociativity318,`AffineCocycleLine318]
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
  unless found == modules.size do throwError "Missing imported modules: {found}/{modules.size}"
  logInfo m!"EXPERIMENT_AUDIT_PASS declarations={count} modules={found}"
