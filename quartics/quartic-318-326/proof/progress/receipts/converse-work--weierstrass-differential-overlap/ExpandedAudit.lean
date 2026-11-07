module
import all UnitDifferential318
import all ShortInfinityDifferential318
import all ActualDifferentialOverlap318
import all DifferentialChartMaps318
import all AlgHomDifferential318
import all InvariantChartForms318
import all InvariantFormFrames318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let wanted := #[ `UnitDifferential318, `ShortInfinityDifferential318, `ActualDifferentialOverlap318, `DifferentialChartMaps318, `AlgHomDifferential318, `InvariantChartForms318, `InvariantFormFrames318 ]
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if wanted.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == wanted.size do throwError "Missing project modules"
  logInfo m!"WEIERSTRASS_DIFFERENTIAL_OVERLAP_AUDIT_PASS declarations={checked} modules={found}"
