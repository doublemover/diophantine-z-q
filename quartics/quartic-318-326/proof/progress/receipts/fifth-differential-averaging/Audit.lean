module
import all FifthFixingSigns318
import all FifthDifferentialAveraging318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`FifthFixingSigns318,`FifthDifferentialAveraging318]
  for name in #[`FifthFixingSigns318.cardinality,`FifthFixingSigns318.mem_iff_fixed,`FifthFixingSigns318.maps_injective,`FifthFixingSigns318.complementary_sum,`FifthFixingSigns318.full_sum,`FifthDifferentialAveraging318.signSum,`FifthDifferentialAveraging318.complementary,`FifthDifferentialAveraging318.fifth,`FifthDifferentialAveraging318.average_add,`FifthDifferentialAveraging318.average_complementary,`FifthDifferentialAveraging318.average_fifth] do
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
  unless found == 2 do throwError "Expected two modules, found {found}"
  logInfo m!"FIFTH_DIFFERENTIAL_AVERAGING_AUDIT_PASS declarations={checked} modules={found}"
