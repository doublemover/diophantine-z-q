module
public import FourRootActualBranchLocalization318
public import ActualEtaleFrameNormalization318
public import SquareCoordinateDifferential318
public import ActualRootPivotCoordinates318
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT imports_processed"
  out.flush
public section
noncomputable section
namespace FourRootActualBranchKaehler318
open Polynomial FourRootActualFiniteBranchChart318 FourRootActualBranchLocalization318
open ActualEtaleFrameNormalization318
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (b:Fin 4→ℂ) (i:Fin 4)
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_polyAlgebra"
  out.flush
local instance polyAlgebra:Algebra ℂ[X] (FourRootActualFractionField318.A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_SourceRing"
  out.flush
abbrev SourceRing:=Localization.Away (denominator b i)
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_baseFrame"
  out.flush
@[expose] def baseFrame:KaehlerDifferential ℂ (BranchBase b i)≃ₗ[BranchBase b i]BranchBase b i:=
  EtaleDifferentialFrame318.ofAlgEquiv
    (LinearRootCoordinate318.coordinateEquiv (1:ℂˣ) (b i)).symm
    (KaehlerDifferential.polynomialEquiv ℂ)
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_openBaseFrame"
  out.flush
@[expose] def openBaseFrame:KaehlerDifferential ℂ (OpenBase b i)≃ₗ[OpenBase b i]OpenBase b i:=by
  letI:=Algebra.FormallyEtale.of_isLocalization (Rₘ:=OpenBase b i)
    (Submonoid.powers (branchDenominator b i))
  exact EtaleDifferentialFrame318.ofFormallyEtale (baseFrame b i)
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_orderFrame"
  out.flush
@[expose] def orderFrame:KaehlerDifferential ℂ (OpenOrder b i)≃ₗ[OpenOrder b i]OpenOrder b i:=by
  letI:Algebra.Etale (OpenBase b i) (OpenOrder b i):=(finite_free_etale b i).2.2
  exact EtaleDifferentialFrame318.ofFormallyEtale (openBaseFrame b i)
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_sourceFrame"
  out.flush
/-- An actual free intrinsic cotangent frame on the genuine principal
localization of the SAME five-variable affine quotient. -/
@[expose] def sourceFrame:KaehlerDifferential ℂ (SourceRing b i)≃ₗ[SourceRing b i]SourceRing b i:=
  EtaleDifferentialFrame318.ofAlgEquiv (sourceLocalizationEquiv b i).symm (orderFrame b i)
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_baseCoordinate"
  out.flush
@[expose] def baseCoordinate:BranchBase b i:=
  (LinearRootCoordinate318.coordinateEquiv (1:ℂˣ) (b i)).symm X
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_baseCoordinate_root"
  out.flush
lemma baseCoordinate_root:baseCoordinate b i=
    AdjoinRoot.root (QuadraticPresentation318.polynomial
      (LinearRootCoordinate318.parameter (1:ℂˣ) (b i))):=
  LinearRootCoordinate318.inverse_X (1:ℂˣ) (b i)
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_base_normalized"
  out.flush
lemma base_normalized:baseFrame b i (KaehlerDifferential.D ℂ _ (baseCoordinate b i))=1:=by
  rw [baseFrame,baseCoordinate,ofAlgEquiv_D_image,
    KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X,map_one]
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_orderCoordinate"
  out.flush
@[expose] def orderCoordinate:OpenOrder b i:=
  algebraMap (OpenBase b i) (OpenOrder b i)
    (algebraMap (BranchBase b i) (OpenBase b i) (baseCoordinate b i))
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_order_normalized"
  out.flush
lemma order_normalized:orderFrame b i (KaehlerDifferential.D ℂ _ (orderCoordinate b i))=1:=by
  letI:=Algebra.FormallyEtale.of_isLocalization (Rₘ:=OpenBase b i)
    (Submonoid.powers (branchDenominator b i))
  letI:Algebra.Etale (OpenBase b i) (OpenOrder b i):=(finite_free_etale b i).2.2
  change EtaleDifferentialFrame318.ofFormallyEtale (openBaseFrame b i)
    (KaehlerDifferential.D ℂ _ (algebraMap _ _ _))=1
  rw [ofFormallyEtale_D]
  change algebraMap _ _ (EtaleDifferentialFrame318.ofFormallyEtale (baseFrame b i)
    (KaehlerDifferential.D ℂ _ (algebraMap _ _ _)))=1
  rw [ofFormallyEtale_D,base_normalized,map_one,map_one]
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_sourceCoordinate"
  out.flush
@[expose] def sourceCoordinate:SourceRing b i:=
  (sourceLocalizationEquiv b i).symm (orderCoordinate b i)
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_source_normalized"
  out.flush
lemma source_normalized:sourceFrame b i (KaehlerDifferential.D ℂ _ (sourceCoordinate b i))=1:=by
  rw [sourceFrame,sourceCoordinate,ofAlgEquiv_D_image,order_normalized,map_one]
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_regroup_root"
  out.flush
lemma regroup_root:
    sourceRegroup b i (FourRootAffineCoordinateRing318.coordinate b (some i))=
      algebraMap (BranchBase b i) (RegroupedOrder b i) (baseCoordinate b i):=by
  rw [baseCoordinate_root]
  change _ (FourRootAffineTensorPresentation318.toTensor b
    (FourRootAffineCoordinateRing318.coordinate b (some i)))=_
  rw [FourRootAffineTensorPresentation318.toTensor_root]
  simpa only [FourRootAffineTensorPresentation318.radicand,FourRootPivot318.indices_zero,
    LinearRootCoordinate318.parameter,Units.val_one,map_one,one_mul] using
    ActualRootPivotCoordinates318.regroup_generator (FourRootAffineTensorPresentation318.radicand b) i
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_source_coordinate_original"
  out.flush
/-- No root choice: the normalized coordinate is the literal original
signed generator of the actual quotient ring. -/
lemma source_coordinate_original:
    sourceCoordinate b i=algebraMap (FourRootActualFractionField318.A b) (SourceRing b i)
      (FourRootAffineCoordinateRing318.coordinate b (some i)):=by
  apply (sourceLocalizationEquiv b i).injective
  rw [sourceCoordinate,AlgEquiv.apply_symm_apply,sourceLocalizationEquiv_on_source]
  change orderCoordinate b i=localizedSourceEquiv b i
    (Algebra.TensorProduct.includeRight (sourceRegroup b i
      (FourRootAffineCoordinateRing318.coordinate b (some i))))
  rw [regroup_root,AlgHom.commutes,
    IsScalarTower.algebraMap_apply (BranchBase b i) (OpenBase b i)
      (OpenBase b i⊗[BranchBase b i]RegroupedOrder b i),AlgEquiv.commutes]
  rfl
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_sourceParameter"
  out.flush
@[expose] def sourceParameter:SourceRing b i:=
  algebraMap (FourRootActualFractionField318.A b) (SourceRing b i)
    (FourRootAffineCoordinateRing318.coordinate b none)
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_exact_square"
  out.flush
lemma exact_square:sourceParameter b i-algebraMap ℂ (SourceRing b i) (b i)=
    (sourceCoordinate b i)^2:=by
  apply (sourceLocalizationEquiv b i).injective
  rw [map_sub,map_pow,AlgEquiv.commutes,sourceCoordinate,AlgEquiv.apply_symm_apply]
  rw [sourceParameter,sourceLocalizationEquiv_on_source]
  change sourceMap b i (algebraMap ℂ[X] (FourRootActualFractionField318.A b) X)-_=_
  rw [sourceMap_on_polynomial]
  have h:=congrArg (algebraMap (OpenBase b i) (OpenOrder b i))
    (FourRootActualFiniteBranchChart318.exact_square b i)
  have hC(q:ℂ):algebraMap ℂ[X] (OpenOrder b i) (C q)=algebraMap ℂ (OpenOrder b i) q:=
    (IsScalarTower.algebraMap_apply ℂ ℂ[X] (OpenOrder b i) q).symm
  simpa only [map_sub,map_pow,orderCoordinate,baseCoordinate_root,
    FourRootActualFiniteBranchChart318.root,FiniteBranchChart318.openRoot,
    ←IsScalarTower.algebraMap_apply,hC] using h
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_parameter_differential"
  out.flush
/-- The derivative of the ACTUAL unshifted projective parameter has
coefficient 2z in the normalized intrinsic frame, on the entire chart. -/
theorem parameter_differential:
    KaehlerDifferential.D ℂ (SourceRing b i) (sourceParameter b i)=
      (2*sourceCoordinate b i) • KaehlerDifferential.D ℂ (SourceRing b i) (sourceCoordinate b i):=by
  simpa only [map_one,mul_one] using
    SquareCoordinateDifferential318.D_of_square (sourceParameter b i) (sourceCoordinate b i)
      (b i) (1:ℂ) (by simpa only [map_one,one_mul] using exact_square b i)
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_parameter_coefficient"
  out.flush
theorem parameter_coefficient:
    sourceFrame b i (KaehlerDifferential.D ℂ _ (sourceParameter b i))=2*sourceCoordinate b i:=by
  rw [parameter_differential,map_smul,source_normalized,smul_eq_mul,mul_one]
#eval do
  let out ← IO.getStdout
  out.putStrLn "PEL_KAEHLER_CHECKPOINT before_namespace_end"
  out.flush
end FourRootActualBranchKaehler318
