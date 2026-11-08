module
import all IntrinsicChartLocalMultiple318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`IntrinsicChartLocalMultiple318.section_multiple] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do throwError "Not a proposition: {name}"
  let mut count:Nat:=0
  let mut found:Nat:=0
  for i in [:env.header.modules.size] do
    if env.header.modules[i]!.module==`IntrinsicChartLocalMultiple318 then
      found:=found+1
      for n in env.header.moduleData[i]!.constNames do
        let axs ← collectAxioms n
        for a in axs do
          unless a==``propext || a==``Classical.choice || a==``Quot.sound do
            throwError "Forbidden {a} in {n}"
        logInfo m!"AXIOM_CHECK {n}: {axs}"
        count:=count+1
  unless found==1 do throwError "Expected one module, found {found}"
  logInfo m!"CHART_LOCAL_MULTIPLE_AUDIT_PASS declarations={count} modules={found}"
