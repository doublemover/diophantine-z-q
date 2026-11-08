module
import all LiteralIndependentPairFinite318
import all FiniteEtaleFieldPoints318
import all CartesianSectionPoints318
import all LiteralKernelFieldCard318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`LiteralIndependentPairFinite318,`FiniteEtaleFieldPoints318,`CartesianSectionPoints318,`LiteralKernelFieldCard318]
  for name in #[`LiteralIndependentPairFinite318.finite_etale,`FiniteEtaleFieldPoints318.pointEquiv,`FiniteEtaleFieldPoints318.card_points,`CartesianSectionPoints318.equiv,`CartesianSectionPoints318.isoEquiv,`LiteralKernelFieldCard318.pointEquiv,`LiteralKernelFieldCard318.card_nine] do
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
  unless found == 4 do throwError "Expected four modules, found {found}"
  logInfo m!"KERNEL_FIELD_CARD_AUDIT_PASS declarations={checked} modules={found}"
