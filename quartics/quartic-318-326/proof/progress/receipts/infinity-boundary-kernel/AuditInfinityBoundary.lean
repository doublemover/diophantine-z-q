module
import all InfinityBoundaryDoubling318
import all InfinityBoundaryScheme318
import all InfinityClosedBoundary318
import all InfinityBoundaryTripling318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`InfinityBoundaryDoubling318,`InfinityBoundaryScheme318,`InfinityClosedBoundary318,`InfinityBoundaryTripling318]
  for name in #[`InfinityBoundaryDoubling318.double_neg_iff,`InfinityBoundaryScheme318.doubling,`InfinityBoundaryScheme318.double_neg_iff,`InfinityClosedBoundary318.scheme_zero,`InfinityBoundaryTripling318.tripling_zero_iff,`InfinityBoundaryTripling318.scheme_zero] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == names.size do throwError "Missing module"
  logInfo m!"INFINITY_BOUNDARY_AUDIT_PASS declarations={checked} modules={found}"
