module
import all EtaleDifferentialFrame318
import all ContactDifferentialFrames318
import all ContactFrameNormalization318
import all ContactIntrinsicDifferentials318
import all ContactIntrinsicFrames318
import all IntrinsicTensorSheaf318
import all OpenSheafification318
import all TensorScalarIso318
import all TensorOpenRestriction318
import all TensorSheafFunctor318
import all ContactBicanonicalSheaf318
import all ContactBicanonicalCoefficients318
import all ContactBicanonicalLocalSections318
import all TensorSheafNormalization318
import all ContactBicanonicalFrameNormalization318
import all ContactBranchCoordinate318
import all SquareCoordinateDifferential318
import all ContactBranchDifferential318
import all IntrinsicFrameDerivative318
import all ContactBicanonicalDerivative318
import all ContactDerivativeFrameComparison318
import all ContactBicanonicalSectionNormalization318
import all BicanonicalCoefficientIdentity318
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`EtaleDifferentialFrame318,`ContactDifferentialFrames318,`ContactFrameNormalization318,`ContactIntrinsicDifferentials318,`ContactIntrinsicFrames318,`IntrinsicTensorSheaf318,`OpenSheafification318,`TensorScalarIso318,`TensorOpenRestriction318,`TensorSheafFunctor318,`ContactBicanonicalSheaf318,`ContactBicanonicalCoefficients318,`ContactBicanonicalLocalSections318,`TensorSheafNormalization318,`ContactBicanonicalFrameNormalization318,`ContactBranchCoordinate318,`SquareCoordinateDifferential318,`ContactBranchDifferential318,`IntrinsicFrameDerivative318,`ContactBicanonicalDerivative318,`ContactDerivativeFrameComparison318,`ContactBicanonicalSectionNormalization318,`BicanonicalCoefficientIdentity318]
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
  logInfo m!"INTRINSIC_TENSOR_NORMALIZATION_AUDIT_PASS declarations={count} modules={found}"
