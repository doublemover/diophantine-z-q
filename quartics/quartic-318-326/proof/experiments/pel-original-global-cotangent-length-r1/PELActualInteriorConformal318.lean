module
public import RiemannNormalizedInterior318
public import PELMaximalActualJordanDomain318
public section
noncomputable section
namespace PELActualInteriorConformal318
open Set Metric
open scoped ComplexConjugate
open PELMaximalActualComplexDomain318 PELMaximalActualJordanDomain318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
open PELMaximalHalfOctagonShape318
set_option maxHeartbeats 2400000

@[expose] def centerPoint : upperCut := ⟨(0,1/2),by norm_num [upperCut]⟩
@[expose] def center : ℂ := cutPoint centerPoint

theorem center_mem : center∈openDomain := by
  refine ⟨(cutPoint centerPoint).property,?_⟩
  change centerHomeomorph (coordinates (cutPoint centerPoint))∈strictPolygon
  rw [coordinates_halfPlane,cutPoint_coordinates]
  norm_num [centerPoint,centerHomeomorph,strictPolygon]

theorem center_fixed : -conj center=center := by
  have h := cutPoint_reflection centerPoint
  have hp : PELMaximalHalfOctagonBoundaryAction318.reflectedCut centerPoint=centerPoint := by
    apply Subtype.ext
    simp [PELMaximalHalfOctagonBoundaryAction318.reflectedCut,centerPoint]
  rw [hp] at h
  exact (congrArg (fun τ : QuaternionicJointPeriodTopology318.HalfPlane => (τ:ℂ)) h).symm

/-- The produced chart uses the literal complex coordinate of the ORIGINAL
maximal-normalizer half-cut. Positive derivative normalization is at its
actual reflection-fixed center, not at a level-three parameter point. -/
theorem actual_normalized_conformal_chart :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source=openDomain ∧ e.target=ball 0 1 ∧ e center=0 ∧
      (∀ z∈openDomain,AnalyticAt ℂ e z) ∧ (∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ e.symm w) ∧
      (deriv e center).im=0 ∧ 0<(deriv e center).re :=
  RiemannNormalizedInterior318.exists_normalized_disk openDomain_open actual_domain_simply_connected
    openDomain_ne_univ center_mem

/-- Compact sets INSIDE the target disk have compact actual inverse images
inside the original open domain. Boundary properness is not smuggled into
this statement: it follows from the already constructed continuous inverse. -/
theorem compact_inverse_image (e : OpenPartialHomeomorph ℂ ℂ)
    (hs : e.source=openDomain) (ht : e.target=ball 0 1)
    {K : Set ℂ} (hK : IsCompact K) (hsub : K⊆ball 0 1) :
    IsCompact (openDomain∩e ⁻¹' K) ∧ (openDomain∩e ⁻¹' K)⊆openDomain := by
  have heq : openDomain∩e ⁻¹' K=e.symm '' K := by
    ext z
    constructor
    · rintro ⟨hz,hKz⟩
      exact ⟨e z,hKz,e.left_inv (hs.symm ▸ hz)⟩
    · rintro ⟨w,hw,rfl⟩
      have hwt : w∈e.target := ht.symm ▸ hsub hw
      exact ⟨hs ▸ e.map_target hwt,by simpa only [Set.mem_preimage,e.right_inv hwt] using hw⟩
  refine ⟨?_,inter_subset_left⟩
  rw [heq]
  exact hK.image_of_continuousOn (e.symm.continuousOn.mono (fun w hw => ht.symm ▸ hsub hw))
end PELActualInteriorConformal318
