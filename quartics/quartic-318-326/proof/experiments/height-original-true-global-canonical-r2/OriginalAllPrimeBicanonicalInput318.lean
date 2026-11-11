module
public import OriginalAllPrimeZoomInput318
public import OriginalFiniteZoomBranchMap318
public import OriginalReciprocalZoomBranchMap318
public section
noncomputable section
namespace OriginalAllPrimeBicanonicalInput318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPrimeZoomInput318
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
abbrev coefficients : Fin 4 → K c t := fun i => algebraMap (V c t w) (K c t) (D.coefficients i)
abbrev contacts : Fin 4 → K c t := fun i => algebraMap ℚ (K c t) (LinearContactSquareclass318.contacts i)

theorem contacts_map (i : Fin 4) : algebraMap (V c t w) (K c t)
    (IntegralSourceBranches318.contacts (V c t w) i)=contacts c t i := by
  fin_cases i <;> norm_num [IntegralSourceBranches318.contacts,contacts,LinearContactSquareclass318.contacts]

theorem original_coefficient (i : Fin 4) : algebraMap ℚ (K c t) (c i : ℚ)=
    coefficients c t w D i*(D.multiplier i)^2 := D.original_coefficient i

namespace Input
variable {m : Mode} (I : OriginalAllPrimeZoomInput318.Input c t w D m)
abbrev fieldCoordinate := algebraMap (V c t w) (K c t) I.coordinate
abbrev fieldRoots : Fin 4 → K c t := fun i => algebraMap (V c t w) (K c t) (I.root i)
theorem fieldRoots_ne (i : Fin 4) : I.fieldRoots i≠0 := by
  simpa only [map_zero] using (IsFractionRing.injective (V c t w) (K c t)).ne (I.root_ne i)
end Input

theorem finite_root_equation (I : OriginalAllPrimeZoomInput318.Input c t w D .finite) (i : Fin 4) :
    (I.fieldRoots i)^2=IntegralQuadraticPointZoom318.value
      (IntegralContactZoomCoefficients318.alpha (coefficients c t w D) (contacts c t) .finite)
      (coefficients c t w D)
      (IntegralContactZoomCoefficients318.gamma (coefficients c t w D) (contacts c t) .finite)
      I.fieldCoordinate i := by
  have h := congrArg (algebraMap (V c t w) (K c t)) (I.root_equation i)
  simpa only [Input.fieldRoots,Input.fieldCoordinate,IntegralQuadraticPointZoom318.value,
    OriginalAllPrimeZoomInput318.alpha,OriginalAllPrimeZoomInput318.beta,OriginalAllPrimeZoomInput318.gamma,
    IntegralContactZoomCoefficients318.alpha,IntegralContactZoomCoefficients318.gamma,
    coefficients,map_add,map_mul,map_pow,map_zero,map_neg,contacts_map] using h

theorem reciprocal_root_equation (I : OriginalAllPrimeZoomInput318.Input c t w D .reciprocal) (i : Fin 4) :
    (I.fieldRoots i)^2=IntegralQuadraticPointZoom318.value
      (IntegralContactZoomCoefficients318.alpha (coefficients c t w D) (contacts c t) .reciprocal)
      (coefficients c t w D)
      (IntegralContactZoomCoefficients318.gamma (coefficients c t w D) (contacts c t) .reciprocal)
      I.fieldCoordinate i := by
  have h := congrArg (algebraMap (V c t w) (K c t)) (I.root_equation i)
  simpa only [Input.fieldRoots,Input.fieldCoordinate,IntegralQuadraticPointZoom318.value,
    OriginalAllPrimeZoomInput318.alpha,OriginalAllPrimeZoomInput318.beta,OriginalAllPrimeZoomInput318.gamma,
    IntegralContactZoomCoefficients318.alpha,IntegralContactZoomCoefficients318.gamma,
    coefficients,map_add,map_mul,map_pow,map_zero,map_neg,contacts_map] using h

/-- Actual original branch map for the finite mode. Every squareclass
coefficient and multiplier is supplied by the SAME produced Data. -/
@[expose] def finiteBranchMap (I : OriginalAllPrimeZoomInput318.Input c t w D .finite) (i : Fin 4) :=
  OriginalFiniteZoomBranchMap318.branchMap c (coefficients c t w D) I.fieldCoordinate
    I.fieldRoots D.multiplier D.multiplier_ne (original_coefficient c t w D)
    (finite_root_equation c t w D I) (I.fieldRoots_ne) i

@[expose] def reciprocalBranchMap (I : OriginalAllPrimeZoomInput318.Input c t w D .reciprocal) (i : Fin 4) :=
  OriginalReciprocalZoomBranchMap318.branchMap c (coefficients c t w D) I.fieldCoordinate
    I.fieldRoots D.multiplier D.multiplier_ne (original_coefficient c t w D)
    (reciprocal_root_equation c t w D I) (I.fieldRoots_ne) i

theorem finite_original_q0 (I : OriginalAllPrimeZoomInput318.Input c t w D .finite) (i : Fin 4) :
    IntegralContactZoomCoefficients318.section0 (coefficients c t w D) (contacts c t) I.fieldCoordinate .finite=
      ContactBicanonicalGenericPullback318.branchImage c i (finiteBranchMap c t w D I i) :=
  OriginalFiniteZoomBranchMap318.original_q0 c (coefficients c t w D) I.fieldCoordinate
    I.fieldRoots D.multiplier D.multiplier_ne (original_coefficient c t w D)
    (finite_root_equation c t w D I) (I.fieldRoots_ne) i

theorem reciprocal_original_q0 (I : OriginalAllPrimeZoomInput318.Input c t w D .reciprocal) (i : Fin 4) :
    IntegralContactZoomCoefficients318.section0 (coefficients c t w D) (contacts c t) I.fieldCoordinate .reciprocal=
      ContactBicanonicalGenericPullback318.branchImage c i (reciprocalBranchMap c t w D I i) :=
  OriginalReciprocalZoomBranchMap318.original_q0 c (coefficients c t w D) I.fieldCoordinate
    I.fieldRoots D.multiplier D.multiplier_ne (original_coefficient c t w D)
    (reciprocal_root_equation c t w D I) (I.fieldRoots_ne) i
end OriginalAllPrimeBicanonicalInput318
