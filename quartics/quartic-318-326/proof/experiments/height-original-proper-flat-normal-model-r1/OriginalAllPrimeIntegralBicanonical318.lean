module
public import OriginalAllPrimeBicanonicalInput318
public import OriginalZoomMarkedSectionComparison318
public import IntegralContactZoomTensorBaseChange318
public section
noncomputable section
namespace OriginalAllPrimeIntegralBicanonical318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open scoped TensorProduct
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
  {m : OriginalAllPrimeZoomInput318.Mode} (I : OriginalAllPrimeZoomInput318.Input c t w D m)
@[expose] def mode : OriginalAllPrimeZoomInput318.Mode → IntegralContactZoomCoefficients318.Mode
  | .finite => .finite
  | .reciprocal => .reciprocal
abbrev contacts := IntegralSourceBranches318.contacts (V c t w)
abbrev IntegralChart := IntegralContactZoomCoefficients318.Chart D.coefficients (contacts c t w) I.coordinate (mode m)
abbrev ChangedChart := IntegralContactZoomBaseChange318.Changed (S:=K c t)
  D.coefficients (contacts c t w) I.coordinate (mode m)

/-- This is the SAME integral point neighborhood previously constructed,
not another model chosen to make section values integral. -/
@[expose] def chartIdentification : I.Chart ≃ₐ[V c t w] IntegralChart c t w D I := by
  cases m <;> exact AlgEquiv.refl

theorem integral_root_equation (i : Fin 4) : (I.root i)^2=
    IntegralQuadraticPointZoom318.value
      (IntegralContactZoomCoefficients318.alpha D.coefficients (contacts c t w) (mode m)) D.coefficients
      (IntegralContactZoomCoefficients318.gamma D.coefficients (contacts c t w) (mode m)) I.coordinate i := by
  cases m <;> exact I.root_equation i

theorem field_root_ne (i : Fin 4) : algebraMap (V c t w) (K c t) (I.root i)≠0 := by
  simpa only [map_zero] using (IsFractionRing.injective (V c t w) (K c t)).ne (I.root_ne i)

theorem contacts_identification :
    IntegralContactZoomBaseChange318.mapped (S:=K c t) (contacts c t w)=
      fun i => algebraMap ℚ (K c t) (LinearContactSquareclass318.contacts i) := by
  funext i
  exact OriginalAllPrimeBicanonicalInput318.contacts_map c t w i

theorem field_root_equation (i : Fin 4) :
    (algebraMap (V c t w) (K c t) (I.root i))^2=
    IntegralQuadraticPointZoom318.value
      (IntegralContactZoomCoefficients318.alpha
        (IntegralContactZoomBaseChange318.mapped (S:=K c t) D.coefficients)
        (IntegralContactZoomBaseChange318.mapped (S:=K c t) (contacts c t w)) (mode m))
      (IntegralContactZoomBaseChange318.mapped (S:=K c t) D.coefficients)
      (IntegralContactZoomCoefficients318.gamma
        (IntegralContactZoomBaseChange318.mapped (S:=K c t) D.coefficients)
        (IntegralContactZoomBaseChange318.mapped (S:=K c t) (contacts c t w)) (mode m))
      (algebraMap (V c t w) (K c t) I.coordinate) i :=
  IntegralContactZoomBaseChange318.mapped_root_equation D.coefficients (contacts c t w) I.coordinate
    (mode m) I.root (integral_root_equation c t w D I) i

@[expose] def originalBranchMap (i : Fin 4) :
    ContactBicanonicalCoefficients318.BranchRing c i →ₐ[ℚ] ChangedChart c t w D I :=
  OriginalZoomMarkedSectionComparison318.branchMap c
    (IntegralContactZoomBaseChange318.mapped (S:=K c t) D.coefficients)
    (IntegralContactZoomBaseChange318.mapped (S:=K c t) (contacts c t w))
    (algebraMap (V c t w) (K c t) I.coordinate) (mode m)
    (fun j => algebraMap (V c t w) (K c t) (I.root j)) D.multiplier
    (contacts_identification c t w) D.multiplier_ne D.original_coefficient
    (field_root_equation c t w D I) (field_root_ne c t w D I) i

@[expose] def integralSection0 := IntegralContactZoomCoefficients318.section0
  D.coefficients (contacts c t w) I.coordinate (mode m)
@[expose] def integralSection1 := IntegralContactZoomCoefficients318.section1
  D.coefficients (contacts c t w) I.coordinate (mode m)
@[expose] def genericSection0 := IntegralContactZoomTensorBaseChange318.genericSection0 (K:=K c t)
  D.coefficients (contacts c t w) I.coordinate (mode m)
@[expose] def genericSection1 := IntegralContactZoomTensorBaseChange318.genericSection1 (K:=K c t)
  D.coefficients (contacts c t w) I.coordinate (mode m)

/-- Actual generic image of the constructed integral q0 tensor section is
exactly the literal original branch coefficient and original differential.
All map, point, coefficient, root-sign and base-change inputs are produced. -/
theorem original_q0 (i : Fin 4) : genericSection0 c t w D I=
    ContactBicanonicalGenericPullback318.branchImage c i (originalBranchMap c t w D I i) := by
  rw [genericSection0,IntegralContactZoomTensorBaseChange318.genericSection0_eq
    D.coefficients (contacts c t w) I.coordinate (mode m) I.root
    (integral_root_equation c t w D I) (field_root_ne c t w D I)]
  exact OriginalZoomMarkedSectionComparison318.q0_identification _ _ _ _ _ _ _ _ _ _ _ _ i

theorem original_q1 (i : Fin 4) : genericSection1 c t w D I=
    originalBranchMap c t w D I i (ContactBicanonicalCoefficients318.branchQ1 c i) •
      (KaehlerDifferential.D (K c t) (ChangedChart c t w D I)
        (originalBranchMap c t w D I i (ContactFrameNormalization318.sourceCoordinate c i)) ⊗ₜ[ChangedChart c t w D I]
        KaehlerDifferential.D (K c t) (ChangedChart c t w D I)
          (originalBranchMap c t w D I i (ContactFrameNormalization318.sourceCoordinate c i))) := by
  rw [genericSection1,IntegralContactZoomTensorBaseChange318.genericSection1_eq
    D.coefficients (contacts c t w) I.coordinate (mode m) I.root
    (integral_root_equation c t w D I) (field_root_ne c t w D I)]
  exact OriginalZoomMarkedSectionComparison318.q1_identification _ _ _ _ _ _ _ _ _ _ _ _ i
end OriginalAllPrimeIntegralBicanonical318
