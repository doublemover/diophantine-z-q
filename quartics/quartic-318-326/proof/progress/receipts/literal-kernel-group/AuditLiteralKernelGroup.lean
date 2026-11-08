module
import all LiteralTriplingHom318
import all LiteralKernelSchemePoints318
import all LiteralKernelScalar318
import all LiteralKernelAddition318
import all LiteralKernelFunctor318
import all LiteralTriplingAdditive318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`LiteralTriplingHom318,`LiteralKernelSchemePoints318,`LiteralKernelScalar318,`LiteralKernelAddition318,`LiteralKernelFunctor318,`LiteralTriplingAdditive318]
  for name in #[`LiteralTriplingHom318.three_value,`LiteralKernelSchemePoints318.equiv,`LiteralKernelSchemePoints318.group,`LiteralKernelScalar318.module,`LiteralKernelScalar318.diamond_val,`LiteralKernelAddition318.addition_inclusion,`LiteralKernelAddition318.addition_value,`LiteralKernelFunctor318.precomposeLinear,`LiteralTriplingAdditive318.additive] do
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
  unless found == 6 do throwError "Expected six modules, found {found}"
  logInfo m!"LITERAL_KERNEL_GROUP_AUDIT_PASS declarations={checked} modules={found}"
