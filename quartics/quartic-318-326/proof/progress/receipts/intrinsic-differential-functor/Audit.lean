module
import all IntrinsicDifferentialFunctor318
import all IntrinsicDifferentialIso318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`IntrinsicDifferentialFunctor318,`IntrinsicDifferentialIso318]
  for name in #[`IntrinsicDifferentialFunctor318.map_comp,`IntrinsicDifferentialFunctor318.map_id,`IntrinsicDifferentialFunctor318.globalSection_comp,`IntrinsicDifferentialFunctor318.globalSection_id,`IntrinsicDifferentialFunctor318.globalSection_congr,`IntrinsicDifferentialFunctor318.globalHom,`IntrinsicDifferentialFunctor318.globalSection_neg,`IntrinsicDifferentialIso318.globalEquiv,`IntrinsicDifferentialIso318.globalEquiv_apply,`IntrinsicDifferentialIso318.globalEquiv_symm_apply,`IntrinsicDifferentialIso318.identity,`IntrinsicDifferentialIso318.composition] do
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
  logInfo m!"INTRINSIC_DIFFERENTIAL_FUNCTOR_AUDIT_PASS declarations={checked} modules={found}"
