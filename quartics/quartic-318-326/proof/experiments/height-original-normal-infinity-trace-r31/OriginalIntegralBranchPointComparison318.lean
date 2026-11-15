module
public import OriginalZoomWholeBranchPoint318
public import OriginalZoomIntegralFiber318
public section
noncomputable section
namespace OriginalIntegralBranchPointComparison318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j,RationalContactPoint318.parameters c t j≠0)
  (w : FinitePlace (K c t)) (D : Data c t w)
  {m : OriginalAllPrimeZoomInput318.Mode} (I : OriginalAllPrimeZoomInput318.Input c t w D m)
@[expose] def evaluation : OriginalAllPrimeIntegralBicanonical318.ChangedChart c t w D I →ₐ[ℚ] K c t :=
  OriginalZoomWholeBranchPoint318.evaluation c t
    (IntegralContactZoomBaseChange318.mapped (S:=K c t) D.coefficients)
    (IntegralContactZoomBaseChange318.mapped (S:=K c t) (OriginalAllPrimeIntegralBicanonical318.contacts c t w))
    (algebraMap (V c t w) (K c t) I.coordinate) (OriginalAllPrimeIntegralBicanonical318.mode m)

theorem original_root (j : Fin 4) : OriginalZoomWholeBranchPoint318.originalRootValue c t
    (fun k => algebraMap (V c t w) (K c t) (I.root k)) D.multiplier
    (algebraMap (V c t w) (K c t) I.coordinate) (OriginalAllPrimeIntegralBicanonical318.mode m) j=
      RationalFourRootFiber318.root (RationalContactPoint318.parameters c t) j := by
  cases m with
  | finite =>
      change D.multiplier j*algebraMap (V c t w) (K c t) (I.root j)=_
      rw [I.root_value]
      change D.multiplier j*(roots c t j/D.multiplier j)=roots c t j
      field_simp [D.multiplier_ne j]
  | reciprocal =>
      have hi : I.coordinate≠0 := IntegralZoomPointCoefficient318.reciprocal_coordinate_ne
        I.coordinate D.coefficients (OriginalAllPrimeIntegralBicanonical318.contacts c t w) I.root I.root_ne
        (OriginalAllPrimeIntegralBicanonical318.integral_root_equation c t w D I)
      have hv : algebraMap (V c t w) (K c t) I.coordinate≠0 := by
        simpa only [map_zero] using (IsFractionRing.injective (V c t w) (K c t)).ne hi
      have ht : (t : K c t)≠0 := by
        rw [I.coordinate_value] at hv
        exact inv_ne_zero_iff.mp hv
      change D.multiplier j*(algebraMap (V c t w) (K c t) I.coordinate)⁻¹*
        algebraMap (V c t w) (K c t) (I.root j)=_
      rw [I.coordinate_value,I.root_value]
      change D.multiplier j*((t : K c t)⁻¹)⁻¹*(roots c t j/(D.multiplier j*(t : K c t)))=roots c t j
      rw [inv_inv]
      field_simp [D.multiplier_ne j,ht]

/-- This is the literal actual generic branch-map/point square. All
original scalar, coordinate and signed-root data have been produced. -/
theorem whole_original_branch_point (i : Fin 4) : (evaluation c t w D I).toRingHom.comp
    (OriginalAllPrimeIntegralBicanonical318.originalBranchMap c t w D I i).toRingHom=
      ContactBranchPoint318.branchPoint c t hn i := by
  apply OriginalZoomWholeBranchPoint318.whole_branch_point c t hn
    (IntegralContactZoomBaseChange318.mapped (S:=K c t) D.coefficients)
    (IntegralContactZoomBaseChange318.mapped (S:=K c t) (OriginalAllPrimeIntegralBicanonical318.contacts c t w))
    (fun j => algebraMap (V c t w) (K c t) (I.root j)) D.multiplier
    (algebraMap (V c t w) (K c t) I.coordinate) (OriginalAllPrimeIntegralBicanonical318.mode m)
    (OriginalAllPrimeIntegralBicanonical318.contacts_identification c t w) D.multiplier_ne
    D.original_coefficient (OriginalAllPrimeIntegralBicanonical318.field_root_equation c t w D I)
    (OriginalAllPrimeIntegralBicanonical318.field_root_ne c t w D I)
  · cases m <;> simpa only [OriginalAllPrimeIntegralBicanonical318.mode,
      OriginalAllPrimeZoomInput318.fieldCoordinate,map_ratCast] using I.coordinate_value
  · exact original_root c t w D I
end OriginalIntegralBranchPointComparison318
