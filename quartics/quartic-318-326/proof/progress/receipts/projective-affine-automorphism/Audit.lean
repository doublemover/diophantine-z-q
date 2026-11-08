module
import all GradedAffineLine318
import all ProjectiveAffineLine318
import all ProjectiveAffineCharts318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`GradedAffineLine318,`ProjectiveAffineLine318,`ProjectiveAffineCharts318]
  for name in #[`GradedAffineLine318.hom_inverse,`GradedAffineLine318.inverse_hom,`ProjectiveAffineLine318.iso,`ProjectiveAffineLine318.map_inverse,`ProjectiveAffineLine318.inverse_map,`ProjectiveAffineCharts318.map_over_base,`ProjectiveAffineCharts318.chart_naturality] do
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
  logInfo m!"PROJECTIVE_AFFINE_AUDIT_PASS declarations={checked} modules={found}"
