module
import all PELQuaternionAlgebra318
import all PELQuaternionAlternatingForm318
import all PELQuaternionRealRepresentation318
import all PELQuaternionIntegralOrder318
import all PELPrincipalOrderCoordinates318
import all PELPrincipalOrderPerfect318
import all PELQuaternionAnisotropy318
import all PELQuaternionDivision318
import all PELOrderTraceDiscriminant318
import all PELTraceDualResidues318
import all PELTraceDualSaturation318
import all PELIntegralOverorder318
import all PELQuadraticIntegralInvariants318
import all PELQuaternionQuadraticCarrier318
import all PELQuaternionIntegralInvariants318
import all PELMaximalIntegralOrder318
import all PELOrderReductionThree318
import all PELReductionResidueField318
import all PELActualLevelThreeQuotient318
import all QuaternionicRealPeriod318
import all QuaternionicHodgeKernel318
import all QuaternionicPeriodVariation318
import all QuaternionicOrderPeriodQuotient318
import all QuaternionicPeriodAlternating318
import all PELQuaternionPeriodOrientation318
import all QuaternionicMatrixCoordinates318
import all PELOriginalPeriodLattice318
import all PELPeriodRiemannForm318
import all PELOriginalThirdPeriods318
import all PELOriginalThreeTorsion318
import all PELThreeTorsionOrderAction318
import all PELLevelThreeCoordinates318
import all PELLevelThreeAlternatingPair318
import all PELPeriodTorsionPolarization318
import all RegularLeftModuleAutomorphisms318
import all PELOriginalLevelMarkings318
import all PELLevelThreeSimilitudes318
import all PELPrimeNormalizerData318
import all PELPrimeOrderConjugation318
import all PELPrimeNormalizerRelations318
import all PELInertiaNormalizerData318
import all PELInertiaOrderInvolutions318
import all PELInertiaQuadraticEmbeddings318
import all PELInertiaRealFixedPoints318
import all PELInertiaPrimeWord318
import all PELInertiaFivefoldRelation318
import all PELQuaternionNormParity318
import all PELActualOrderNormalizer318
import all PELPositiveOrderNormalizer318
import all PELNormalizerParityQuotient318
import all PELPrimeRightLattice318
import all PELPrimeLatticeResidues318
import all PELPrimeLatticeCokernel318
import all PELNormalizerReductionAction318
import all PELNormalizerResidueFrobenius318
import all PELNormalizerInnerRelations318
import all PELNormalizerProjectiveLevel318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`PELQuaternionAlgebra318,`PELQuaternionAlternatingForm318,`PELQuaternionRealRepresentation318,`PELQuaternionIntegralOrder318,`PELPrincipalOrderCoordinates318,`PELPrincipalOrderPerfect318,`PELQuaternionAnisotropy318,`PELQuaternionDivision318,`PELOrderTraceDiscriminant318,`PELTraceDualResidues318,`PELTraceDualSaturation318,`PELIntegralOverorder318,`PELQuadraticIntegralInvariants318,`PELQuaternionQuadraticCarrier318,`PELQuaternionIntegralInvariants318,`PELMaximalIntegralOrder318,`PELOrderReductionThree318,`PELReductionResidueField318,`PELActualLevelThreeQuotient318,`QuaternionicRealPeriod318,`QuaternionicHodgeKernel318,`QuaternionicPeriodVariation318,`QuaternionicOrderPeriodQuotient318,`QuaternionicPeriodAlternating318,`PELQuaternionPeriodOrientation318,`QuaternionicMatrixCoordinates318,`PELOriginalPeriodLattice318,`PELPeriodRiemannForm318,`PELOriginalThirdPeriods318,`PELOriginalThreeTorsion318,`PELThreeTorsionOrderAction318,`PELLevelThreeCoordinates318,`PELLevelThreeAlternatingPair318,`PELPeriodTorsionPolarization318,`RegularLeftModuleAutomorphisms318,`PELOriginalLevelMarkings318,`PELLevelThreeSimilitudes318,`PELPrimeNormalizerData318,`PELPrimeOrderConjugation318,`PELPrimeNormalizerRelations318,`PELInertiaNormalizerData318,`PELInertiaOrderInvolutions318,`PELInertiaQuadraticEmbeddings318,`PELInertiaRealFixedPoints318,`PELInertiaPrimeWord318,`PELInertiaFivefoldRelation318,`PELQuaternionNormParity318,`PELActualOrderNormalizer318,`PELPositiveOrderNormalizer318,`PELNormalizerParityQuotient318,`PELPrimeRightLattice318,`PELPrimeLatticeResidues318,`PELPrimeLatticeCokernel318,`PELNormalizerReductionAction318,`PELNormalizerResidueFrobenius318,`PELNormalizerInnerRelations318,`PELNormalizerProjectiveLevel318]
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
