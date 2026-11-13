module
public import IntegralModelDualRealization318
public import OriginalAllPrimeFiniteDuality318
public section
noncomputable section
namespace OriginalAllPrimeDualSectionComparison318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPrimeIntegralBicanonical318
open FiniteDualTransport318
open scoped TensorProduct
set_option maxHeartbeats 2400000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
  {m : OriginalAllPrimeZoomInput318.Mode} (I : OriginalAllPrimeZoomInput318.Input c t w D m)
local notation "V" => OriginalPointFinitePlaceRoots318.V c t w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "μ" => OriginalAllPrimeIntegralBicanonical318.mode m
abbrev ModelOrder := IntegralModelDualRealization318.Order D.coefficients a μ

/-- Literal integral model tensor sections, on the actual finite or
reciprocal WHOLE model order selected by the original arithmetic point. -/
@[expose] def modelSection0 : Square (R:=V[X]) (A:=ModelOrder c t w D (m:=m)) :=
  IntegralModelDualRealization318.modelSection D.coefficients a μ
    (IntegralModelDualRealization318.polynomial0 D.coefficients μ)
@[expose] def modelSection1 : Square (R:=V[X]) (A:=ModelOrder c t w D (m:=m)) :=
  IntegralModelDualRealization318.modelSection D.coefficients a μ
    (IntegralModelDualRealization318.polynomial1 D.coefficients μ)

@[expose] def modelRealization := IntegralModelDualRealization318.realization (K:=K c t)
  D.coefficients a I.coordinate μ I.root (integral_root_equation c t w D I)
    (field_root_ne c t w D I)

/-- The image is the SAME actual generic zoom tensor already compared
with the original marked branch, not an abstract isomorphic line. -/
theorem section0_image : modelRealization c t w D I (modelSection0 c t w D (m:=m))=
    genericSection0 c t w D I := by
  rw [modelRealization,modelSection0,IntegralModelDualRealization318.section0_image]
  exact (IntegralContactZoomTensorBaseChange318.genericSection0_eq
    D.coefficients a I.coordinate μ I.root (integral_root_equation c t w D I)
      (field_root_ne c t w D I)).symm

theorem section1_image : modelRealization c t w D I (modelSection1 c t w D (m:=m))=
    genericSection1 c t w D I := by
  rw [modelRealization,modelSection1,IntegralModelDualRealization318.section1_image]
  exact (IntegralContactZoomTensorBaseChange318.genericSection1_eq
    D.coefficients a I.coordinate μ I.root (integral_root_equation c t w D I)
      (field_root_ne c t w D I)).symm

/-- At EVERY original finite place, the constructed integral model-dual
section maps through a genuine balanced tensor map to the literal original
q0 on each original branch chart, with all original source maps retained. -/
theorem original_q0 (i : Fin 4) :
    modelRealization c t w D I (modelSection0 c t w D (m:=m))=
      ContactBicanonicalGenericPullback318.branchImage c i (originalBranchMap c t w D I i) := by
  rw [section0_image,OriginalAllPrimeIntegralBicanonical318.original_q0]

theorem original_q1 (i : Fin 4) :
    modelRealization c t w D I (modelSection1 c t w D (m:=m))=
      originalBranchMap c t w D I i (ContactBicanonicalCoefficients318.branchQ1 c i) •
        (KaehlerDifferential.D (K c t) (ChangedChart c t w D I)
          (originalBranchMap c t w D I i (ContactFrameNormalization318.sourceCoordinate c i)) ⊗ₜ[ChangedChart c t w D I]
        KaehlerDifferential.D (K c t) (ChangedChart c t w D I)
          (originalBranchMap c t w D I i (ContactFrameNormalization318.sourceCoordinate c i))) := by
  rw [section1_image,OriginalAllPrimeIntegralBicanonical318.original_q1]
end OriginalAllPrimeDualSectionComparison318
