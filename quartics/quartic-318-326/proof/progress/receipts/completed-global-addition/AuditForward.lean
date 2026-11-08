module
import all GenericOpenPushout318
import all WeierstrassChartPullback318
import all CompletedAdditionCharts318
import all WholeBothNaturality318
import all ChartInputEquality318
import all AlgebraChartEvaluation318
import all AlgebraChartEdges318
import all AlgebraChartCompatibility318
import all AffineProductEvaluation318
import all ChartPointEvaluation318
import all ChartSchemeCompatibility318
import all CompletedAdditionCompatibility318
import all CompletedAddition318
import all CompletedAdditionRestrictions318
import all CompletedIteratedAddition318
import all CompletedAdditionTriple318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`GenericOpenPushout318,`WeierstrassChartPullback318,`CompletedAdditionCharts318,`WholeBothNaturality318,`ChartInputEquality318,`AlgebraChartEvaluation318,`AlgebraChartEdges318,`AlgebraChartCompatibility318,`AffineProductEvaluation318,`ChartPointEvaluation318,`ChartSchemeCompatibility318,`CompletedAdditionCompatibility318,`CompletedAddition318,`CompletedAdditionRestrictions318,`CompletedIteratedAddition318,`CompletedAdditionTriple318]
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
  logInfo m!"COMPLETED_ADDITION_FORWARD_AUDIT_PASS declarations={checked} modules={found}"
