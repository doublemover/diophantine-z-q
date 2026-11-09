module
import all FlatGlobalSections318
import all UniversalStructurePushforward318
import all GeometricIntegralConstants318
import all ActualSourceRationalConstants318
import all ContactUniversalGlobalFunctions318
import all TensorPullbackCocycle318
import all LineClassPullbackHom318
import all RelativeLineClassQuotient318
import all RelativeLineClassBaseChange318
import all RelativeLineSectionNormalization318
import all RelativeRigidifiedLine318
import all RelativeSectionBaseChange318
import all UniversalSectionEvaluation318
import all FourRootPointTorsor318
import all RationalFourRootFiber318
import all RationalContactPoint318
import all ContactFieldSection318
import all OriginalLineAutomorphismLocal318
import all OriginalLineAutomorphismScalar318
import all OriginalLineAutomorphismEquiv318
import all OriginalModuleScalarPullback318
import all OriginalLineAutPullback318
import all OriginalLineAutPullbackEquiv318
import all RigidifiedLineIsomorphism318
import all RigidifiedRelativeClass318
import all ContactUniversalRigidifiedClass318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`FlatGlobalSections318,`UniversalStructurePushforward318,`GeometricIntegralConstants318,`ActualSourceRationalConstants318,`ContactUniversalGlobalFunctions318,`TensorPullbackCocycle318,`LineClassPullbackHom318,`RelativeLineClassQuotient318,`RelativeLineClassBaseChange318,`RelativeLineSectionNormalization318,`RelativeRigidifiedLine318,`RelativeSectionBaseChange318,`UniversalSectionEvaluation318,`FourRootPointTorsor318,`RationalFourRootFiber318,`RationalContactPoint318,`ContactFieldSection318,`OriginalLineAutomorphismLocal318,`OriginalLineAutomorphismScalar318,`OriginalLineAutomorphismEquiv318,`OriginalModuleScalarPullback318,`OriginalLineAutPullback318,`OriginalLineAutPullbackEquiv318,`RigidifiedLineIsomorphism318,`RigidifiedRelativeClass318,`ContactUniversalRigidifiedClass318]
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
