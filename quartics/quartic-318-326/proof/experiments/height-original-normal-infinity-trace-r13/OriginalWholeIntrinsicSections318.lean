module
public import NormalizedWholeTensorSections318
public import OriginalWholeDualityModel318
public section
noncomputable section
namespace OriginalWholeIntrinsicSections318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalWholeDualityModel318 OriginalAllPrimeDualSectionComparison318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
local notation "V" => OriginalPointFinitePlaceRoots318.V c t w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "L" => canonicalCandidate c t w D
@[expose] def tensorSquare : D.model.Modules := IntrinsicTensorSheaf318.tensor L L

/-- SAME original proper arithmetic model, SAME original line and actual
intrinsic sheafified square, now genuinely isomorphic to the constructed
whole-model bicanonical candidate. No dualizing identification is presumed. -/
@[expose] def comparison : tensorSquare c t w D ≅ bicanonicalCandidate c t w D :=
  NormalizedWholeIntrinsicTensor318.iso V D.coefficients a
@[expose] def global0 : Γ(tensorSquare c t w D,⊤) :=
  NormalizedWholeIntrinsicTensor318.section0 V D.coefficients a
@[expose] def global1 : Γ(tensorSquare c t w D,⊤) :=
  NormalizedWholeIntrinsicTensor318.section1 V D.coefficients a

/-- Restrict an arbitrary global intrinsic tensor section to the actual
whole model chart selected by the original point, retaining its true frame
and actual affine scalar comparison. -/
@[expose] def modelTensor (m : OriginalAllPrimeZoomInput318.Mode)
    (s : Γ(tensorSquare c t w D,⊤)) :
    FiniteDualTransport318.Square (R:=V[X]) (A:=ModelOrder c t w D (m:=m)) := by
  cases m with
  | finite => exact NormalizedWholeTensorSections318.finiteTensor V D.coefficients a s
  | reciprocal => exact NormalizedWholeTensorSections318.infinityTensor V D.coefficients a s

lemma global0_model (m : OriginalAllPrimeZoomInput318.Mode) :
    modelTensor c t w D m (global0 c t w D) = modelSection0 c t w D (m:=m) := by
  cases m with
  | finite => exact NormalizedWholeTensorSections318.section0_finite V D.coefficients a
  | reciprocal => exact NormalizedWholeTensorSections318.section0_infinity V D.coefficients a
lemma global1_model (m : OriginalAllPrimeZoomInput318.Mode) :
    modelTensor c t w D m (global1 c t w D) = modelSection1 c t w D (m:=m) := by
  cases m with
  | finite => exact NormalizedWholeTensorSections318.section1_finite V D.coefficients a
  | reciprocal => exact NormalizedWholeTensorSections318.section1_infinity V D.coefficients a

variable {m : OriginalAllPrimeZoomInput318.Mode} (I : OriginalAllPrimeZoomInput318.Input c t w D m)
/-- Full composite from actual GLOBAL tensor sections through actual whole
integral model dual tensors and the already verified balanced differential
map, defined on every global section, not only a prescribed coefficient. -/
@[expose] def differentialImage (s : Γ(tensorSquare c t w D,⊤)) :=
  modelRealization c t w D I (modelTensor c t w D m s)

theorem global0_original (i : Fin 4) : differentialImage c t w D I (global0 c t w D) =
    ContactBicanonicalGenericPullback318.branchImage c i
      (OriginalAllPrimeIntegralBicanonical318.originalBranchMap c t w D I i) := by
  rw [differentialImage,global0_model]
  exact original_q0 c t w D I i

theorem global1_original (i : Fin 4) : differentialImage c t w D I (global1 c t w D) =
    OriginalAllPrimeIntegralBicanonical318.originalBranchMap c t w D I i
      (ContactBicanonicalCoefficients318.branchQ1 c i) •
      (KaehlerDifferential.D (K c t) (OriginalAllPrimeIntegralBicanonical318.ChangedChart c t w D I)
        (OriginalAllPrimeIntegralBicanonical318.originalBranchMap c t w D I i
          (ContactFrameNormalization318.sourceCoordinate c i)) ⊗ₜ[_]
      KaehlerDifferential.D (K c t) (OriginalAllPrimeIntegralBicanonical318.ChangedChart c t w D I)
        (OriginalAllPrimeIntegralBicanonical318.originalBranchMap c t w D I i
          (ContactFrameNormalization318.sourceCoordinate c i))) := by
  rw [differentialImage,global1_model]
  exact original_q1 c t w D I i
end OriginalWholeIntrinsicSections318
