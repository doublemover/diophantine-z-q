module
import all IntrinsicDifferentialPullback318
import all AffineChartPullbackScalars318
import all IntrinsicDifferentialSectionPullback318
import all IntrinsicAffineSectionEquiv318
import all ContactCharacterDifferentials318
import all CharacterCoordinateDifferentials318
import all WeierstrassAffineInvariant318
import all ContactCharacterAffinePullback318
import all WeierstrassFiniteDifferentialEquality318
import all WeierstrassAffineInvariantEquation318
import all CharacterPullbackNormalization318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`IntrinsicDifferentialPullback318,`AffineChartPullbackScalars318,`IntrinsicDifferentialSectionPullback318,`IntrinsicAffineSectionEquiv318,`ContactCharacterDifferentials318,`CharacterCoordinateDifferentials318,`WeierstrassAffineInvariant318,`ContactCharacterAffinePullback318,`WeierstrassFiniteDifferentialEquality318,`WeierstrassAffineInvariantEquation318,`CharacterPullbackNormalization318]
  for name in #[`IntrinsicDifferentialPullback318.map_D,`IntrinsicDifferentialPullback318.pullbackMap_adjoint,`IntrinsicDifferentialSectionPullback318.sectionMap_naturality,`ContactCharacterDifferentials318.differential,`ContactCharacterAffinePullback318.finite_restrict,`WeierstrassAffineInvariantEquation318.equation,`CharacterPullbackNormalization318.finite_equation,`CharacterPullbackNormalization318.intrinsic_finite_equation] do
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
  unless found == 11 do throwError "Expected eleven modules, found {found}"
  logInfo m!"CHARACTER_DIFFERENTIAL_AUDIT_PASS declarations={checked} modules={found}"
