module
import all LiteralSchemePointGroup318
import all LiteralTriplingNegation318
import all LiteralKernelNegation318
import all ThreeTorsionNegationScheme318
import all LiteralKernelDiamond318
import all LiteralKernelDiamondAction318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`LiteralSchemePointGroup318,`LiteralTriplingNegation318,`LiteralKernelNegation318,`ThreeTorsionNegationScheme318,`LiteralKernelDiamond318,`LiteralKernelDiamondAction318]
  for name in #[`LiteralSchemePointGroup318.group,`LiteralTriplingNegation318.commute,`LiteralKernelNegation318.iso,`LiteralKernelNegation318.zero_fixed,`ThreeTorsionNegationScheme318.completed_inclusion,`LiteralKernelDiamond318.finite_compatibility,`LiteralKernelDiamond318.coproduct_equivariance,`LiteralKernelDiamondAction318.diamond_mul,`LiteralKernelDiamondAction318.published_compatibility,`LiteralKernelDiamondAction318.coproduct_equivariance] do
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
  logInfo m!"LITERAL_KERNEL_DIAMOND_AUDIT_PASS declarations={checked} modules={found}"
