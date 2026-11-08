module
import all CharacterFifthCommonMultiple318
import all CharacterBranchLocalForm318
import all CharacterCanonicalCommonRestriction318
import all CharacterBranchCommonSection318
import all CharacterBranchActualRestriction318
import all CharacterInfinityLocalForm318
import all InfinityChartSectionExtension318
import all CharacterInfinityCommonSection318
import all CharacterInfinityActualRestriction318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`CharacterFifthCommonMultiple318,`CharacterBranchLocalForm318,`CharacterCanonicalCommonRestriction318,`CharacterBranchCommonSection318,`CharacterBranchActualRestriction318,`CharacterInfinityLocalForm318,`InfinityChartSectionExtension318,`CharacterInfinityCommonSection318,`CharacterInfinityActualRestriction318]
  for name in #[`CharacterFifthCommonMultiple318.form_eq,`CharacterBranchLocalForm318.frame_unit,`CharacterBranchLocalForm318.omitted_frame_value,`CharacterBranchActualRestriction318.restrict,`CharacterInfinityLocalForm318.coefficient_unit,`CharacterInfinityActualRestriction318.restrict] do
    unless env.contains name do throwError "Missing endpoint {name}"
  let mut n:Nat:=0
  let mut found:Nat:=0
  for idx in [:env.header.modules.size] do
    if mods.contains env.header.modules[idx]!.module then
      found:=found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        n:=n+1
  unless found==9 do throwError "Expected nine modules, found {found}"
  logInfo m!"COMPLEMENTARY_LOCAL_NORMALIZATION_AUDIT_PASS declarations={n} modules={found}"
