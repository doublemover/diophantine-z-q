module
import all QuaternionicRealPeriod318
import all QuaternionicHodgeKernel318
import all QuaternionicPeriodVariation318
import all QuaternionicOrderPeriodQuotient318
import all PELQuaternionAlgebra318
import all PELQuaternionAlternatingForm318
import all PELQuaternionRealRepresentation318
import all PELQuaternionIntegralOrder318
import all PELPrincipalOrderCoordinates318
import all PELPrincipalOrderPerfect318
import all QuaternionicPeriodAlternating318
import all PELQuaternionPeriodOrientation318
import all QuaternionicMatrixCoordinates318
import all PELOriginalPeriodLattice318
import all PELPeriodRiemannForm318
import all DiscreteComplexPeriodAtlas318
import all DiscreteComplexPeriodMaps318
import all PELComplexPeriodSurface318
import all QuaternionicMobiusPeriods318
import all QuaternionicUnitPeriodTransport318
import all DiscreteComplexPeriodEquiv318
import all PELOriginalUnitBiholomorph318
import all QuaternionicPeriodAutomorphy318
import all PELPeriodDeterminant318
import all QuaternionicJointPeriodTopology318
import all PELJointPeriodFamily318
import all PELJointPeriodDeck318
import all PELJointComplexAtlas318
import all PELHolomorphicFamilyProjection318
import all PELOriginalHolomorphicFibers318
import all PELJointArithmeticLift318
import all PELJointArithmeticHolomorphy318
import all PELJointArithmeticCoherence318
import all PELJointNormOneAction318
import all PELQuaternionAnisotropy318
import all PELQuaternionDivision318
import all PELOrderTraceDiscriminant318
import all PELTraceDualResidues318
import all PELTraceDualSaturation318
import all PELIntegralOverorder318
import all QuaternionicFixedParameter318
import all PELPrincipalThreeStabilizer318
import all PELPrincipalThreeFreeAction318
import all PELOriginalDiscreteSLGroup318
import all PELPrincipalProperAction318
import all PELPrincipalThreeCovering318
import all HolomorphicQuotientCoverCharts318
import all HolomorphicQuotientCoverMaps318
import all PELPrincipalBaseHolomorphy318
import all PELArithmeticComplexFamily318
import all PELArithmeticOriginalFibers318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`QuaternionicRealPeriod318,`QuaternionicHodgeKernel318,`QuaternionicPeriodVariation318,`QuaternionicOrderPeriodQuotient318,`PELQuaternionAlgebra318,`PELQuaternionAlternatingForm318,`PELQuaternionRealRepresentation318,`PELQuaternionIntegralOrder318,`PELPrincipalOrderCoordinates318,`PELPrincipalOrderPerfect318,`QuaternionicPeriodAlternating318,`PELQuaternionPeriodOrientation318,`QuaternionicMatrixCoordinates318,`PELOriginalPeriodLattice318,`PELPeriodRiemannForm318,`DiscreteComplexPeriodAtlas318,`DiscreteComplexPeriodMaps318,`PELComplexPeriodSurface318,`QuaternionicMobiusPeriods318,`QuaternionicUnitPeriodTransport318,`DiscreteComplexPeriodEquiv318,`PELOriginalUnitBiholomorph318,`QuaternionicPeriodAutomorphy318,`PELPeriodDeterminant318,`QuaternionicJointPeriodTopology318,`PELJointPeriodFamily318,`PELJointPeriodDeck318,`PELJointComplexAtlas318,`PELHolomorphicFamilyProjection318,`PELOriginalHolomorphicFibers318,`PELJointArithmeticLift318,`PELJointArithmeticHolomorphy318,`PELJointArithmeticCoherence318,`PELJointNormOneAction318,`PELQuaternionAnisotropy318,`PELQuaternionDivision318,`PELOrderTraceDiscriminant318,`PELTraceDualResidues318,`PELTraceDualSaturation318,`PELIntegralOverorder318,`QuaternionicFixedParameter318,`PELPrincipalThreeStabilizer318,`PELPrincipalThreeFreeAction318,`PELOriginalDiscreteSLGroup318,`PELPrincipalProperAction318,`PELPrincipalThreeCovering318,`HolomorphicQuotientCoverCharts318,`HolomorphicQuotientCoverMaps318,`PELPrincipalBaseHolomorphy318,`PELArithmeticComplexFamily318,`PELArithmeticOriginalFibers318]
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        count := count+1
  unless found == modules.size do throwError "Missing imported modules: {found}/{modules.size}"
  logInfo m!"EXPERIMENT_AUDIT_PASS declarations={count} modules={found}"
