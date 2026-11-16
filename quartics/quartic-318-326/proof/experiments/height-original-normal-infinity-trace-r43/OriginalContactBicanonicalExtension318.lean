module
public import OriginalAllPrimeIntegralBicanonical318
public import OriginalContactAllPrimeNeighborhood318
public section
noncomputable section
namespace OriginalContactBicanonicalExtension318
open NumberField OriginalPointFinitePlaceRoots318
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5,ContactRadical318.forms u v j≠0)
  (w : FinitePlace (OriginalContactAllPrimeNeighborhood318.Field c u v))
abbrev t : ℚ := OriginalContactAllPrimeNeighborhood318.coordinate u v
abbrev data := OriginalContactAllPrimeNeighborhood318.data c u v w
abbrev input := OriginalContactAllPrimeNeighborhood318.input c u v hf w
abbrev GenericChart := OriginalAllPrimeIntegralBicanonical318.ChangedChart c (t u v) w
  (data c u v w) (input c u v hf w)

/-- Actual integral extensions on the SAME produced all-prime smooth
point-neighborhood, with exactly the original integer J² scaling. -/
@[expose] def integral0 := ContactScaledBicanonicalPoint318.J^2 •
  OriginalAllPrimeIntegralBicanonical318.integralSection0 c (t u v) w (data c u v w) (input c u v hf w)
@[expose] def integral1 := ContactScaledBicanonicalPoint318.J^2 •
  OriginalAllPrimeIntegralBicanonical318.integralSection1 c (t u v) w (data c u v w) (input c u v hf w)
@[expose] def generic0 := ContactScaledBicanonicalPoint318.J^2 •
  OriginalAllPrimeIntegralBicanonical318.genericSection0 c (t u v) w (data c u v w) (input c u v hf w)
@[expose] def generic1 := ContactScaledBicanonicalPoint318.J^2 •
  OriginalAllPrimeIntegralBicanonical318.genericSection1 c (t u v) w (data c u v w) (input c u v hf w)
@[expose] def originalMap (i : Fin 4) :=
  OriginalAllPrimeIntegralBicanonical318.originalBranchMap c (t u v) w (data c u v w) (input c u v hf w) i

@[expose] def tensorMap := BaseChangingDifferentialTensor318.tensorMap
  (S:=OriginalContactAllPrimeNeighborhood318.Field c u v)
  (IntegralContactZoomBaseChange318.coefficientMap
    (S:=OriginalContactAllPrimeNeighborhood318.Field c u v)
    (data c u v w).coefficients
    (OriginalAllPrimeIntegralBicanonical318.contacts c (t u v) w)
    (input c u v hf w).coordinate
    (OriginalAllPrimeIntegralBicanonical318.mode (OriginalContactAllPrimeNeighborhood318.mode c u v hf w)))

/-- The genuine balanced map sends the LITERAL integral scaled section,
not merely a selected pure-tensor formula, to its generic image. -/
theorem tensorMap_integral0 : tensorMap c u v hf w (integral0 c u v hf w)=generic0 c u v hf w := by
  rw [integral0,map_nsmul]
  change ContactScaledBicanonicalPoint318.J^2 •
    BaseChangingDifferentialTensor318.tensorMap _ (IntegralContactZoomCoefficients318.section0 _ _ _ _)=_
  rw [IntegralContactZoomTensorBaseChange318.tensorMap_section0]
  rfl

theorem tensorMap_integral1 : tensorMap c u v hf w (integral1 c u v hf w)=generic1 c u v hf w := by
  rw [integral1,map_nsmul]
  change ContactScaledBicanonicalPoint318.J^2 •
    BaseChangingDifferentialTensor318.tensorMap _ (IntegralContactZoomCoefficients318.section1 _ _ _ _)=_
  rw [IntegralContactZoomTensorBaseChange318.tensorMap_section1]
  rfl

/-- Exact original scaled branch formula, including both differential
factors, at EVERY finite place of the literal five-form point field. -/
theorem original_scaled_q0 (i : Fin 4) : generic0 c u v hf w=
    originalMap c u v hf w i (ContactScaledBicanonicalPoint318.J^2 • ContactBicanonicalCoefficients318.branchQ0 c i) •
      (KaehlerDifferential.D (OriginalContactAllPrimeNeighborhood318.Field c u v) (GenericChart c u v hf w)
        (originalMap c u v hf w i (ContactFrameNormalization318.sourceCoordinate c i)) ⊗ₜ[GenericChart c u v hf w]
        KaehlerDifferential.D (OriginalContactAllPrimeNeighborhood318.Field c u v) (GenericChart c u v hf w)
          (originalMap c u v hf w i (ContactFrameNormalization318.sourceCoordinate c i))) := by
  rw [generic0,OriginalAllPrimeIntegralBicanonical318.original_q0]
  unfold ContactBicanonicalGenericPullback318.branchImage
  rw [map_nsmul,smul_assoc]

theorem original_scaled_q1 (i : Fin 4) : generic1 c u v hf w=
    originalMap c u v hf w i (ContactScaledBicanonicalPoint318.J^2 • ContactBicanonicalCoefficients318.branchQ1 c i) •
      (KaehlerDifferential.D (OriginalContactAllPrimeNeighborhood318.Field c u v) (GenericChart c u v hf w)
        (originalMap c u v hf w i (ContactFrameNormalization318.sourceCoordinate c i)) ⊗ₜ[GenericChart c u v hf w]
        KaehlerDifferential.D (OriginalContactAllPrimeNeighborhood318.Field c u v) (GenericChart c u v hf w)
          (originalMap c u v hf w i (ContactFrameNormalization318.sourceCoordinate c i))) := by
  rw [generic1,OriginalAllPrimeIntegralBicanonical318.original_q1,map_nsmul,smul_assoc]

/-- The true remaining arithmetic metric boundary is separate: these
local tensor extensions alone do not identify the global regular-model
canonical lattice with the square of the Hodge lattice via210. -/
theorem original_pair_retained (i : Fin 4) :
    ContactBicanonicalPointHeight318.a0 c (t u v)
      (RationalContactPoint318.parameters_ne_of_forms c u v hf) i≠0 ∧
    ContactBicanonicalPointHeight318.a1 c (t u v)
      (RationalContactPoint318.parameters_ne_of_forms c u v hf) i=
      (t u v : OriginalContactAllPrimeNeighborhood318.Field c u v)*
        ContactBicanonicalPointHeight318.a0 c (t u v)
          (RationalContactPoint318.parameters_ne_of_forms c u v hf) i :=
  OriginalContactAllPrimeNeighborhood318.same_original_section_pair c u v hf i
end OriginalContactBicanonicalExtension318
