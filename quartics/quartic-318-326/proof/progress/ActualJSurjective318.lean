module
public import AllCuspCompact318
public import AllCuspInfinity318
public import OpenJLocalComparison318
public import ActualJCusp318
public import Mathlib.Analysis.Complex.OpenMapping
public section
noncomputable section
namespace ActualJSurjective318
open UpperHalfPlane OpenJLocalComparison318
open AllCuspFilling318 AllCuspInfinity318 GammaOneAtlas318
set_option maxHeartbeats 0

/-- The genuine analytic j-image is open: analyticity and the actual cusp
asymptotic rule out the constant alternative in the complex open-mapping theorem. -/
theorem range_isOpen : IsOpen (Set.range ActualQJ318.jInvariant) := by
  have hf : AnalyticOnNhd ℂ j upperHalfPlaneSet := by
    intro z hz
    exact j_analyticAt ⟨z,hz⟩
  rcases hf.is_constant_or_isOpen (convex_halfSpace_im_gt 0).isPreconnected with hc|ho
  · obtain ⟨c,hc⟩ := hc
    exfalso
    apply ActualJCusp318.j_not_constant c
    intro tau
    simpa only [j,UpperHalfPlane.ofComplex_apply] using hc (tau:ℂ) tau.im_pos
  · have he : j '' upperHalfPlaneSet=Set.range ActualQJ318.jInvariant := by
      rw [←UpperHalfPlane.range_coe,←Set.range_comp]
      congr 1
      funext tau
      simp only [Function.comp_apply,j,UpperHalfPlane.ofComplex_apply]
    rw [←he]
    exact ho _ (Set.Subset.refl _) isOpen_upperHalfPlaneSet

/-- Finite values in the image of the actual all-cusp extension are exactly
the values of the genuine upper-half-plane j-function. Every added point is
an actual cusp and maps to infinity. -/
theorem range_eq_finite_image (N : ℕ) (hN : 5≤N) :
    Set.range ActualQJ318.jInvariant=
      (fun z:ℂ => (z:OnePoint ℂ)) ⁻¹' Set.range (jInfinity N hN) := by
  ext z
  constructor
  · rintro ⟨tau,rfl⟩
    exact ⟨original N hN (quotientMap N tau),by rw [jInfinity_original]; rfl⟩
  · rintro ⟨p,hp⟩
    rcases original_or_cusp N hN p with ⟨b,rfl⟩|⟨c,rfl⟩
    · obtain ⟨tau,rfl⟩ := quotient_surjective N b
      rw [jInfinity_original] at hp
      refine ⟨tau,?_⟩
      exact OnePoint.coe_injective hp
    · rw [jInfinity_cusp] at hp
      exact False.elim (OnePoint.infty_ne_coe z hp)

/-- Closedness follows from the proved compactness of the genuine all-cusp
curve, not from an assumed properness or modular classification statement. -/
theorem range_isClosed : IsClosed (Set.range ActualQJ318.jInvariant) := by
  letI := AllCuspCompact318.filled_compactSpace 5 (Nat.le_refl 5)
  rw [range_eq_finite_image 5 (Nat.le_refl 5)]
  exact (isCompact_range (jInfinity_continuous 5 (Nat.le_refl 5))).isClosed.preimage
    OnePoint.continuous_coe

/-- Every complex number is a value of the genuine analytic modular
j-invariant. The proof joins the constructed all-cusp compactification with
actual holomorphic open mapping and genuine cusp nonconstancy. -/
theorem surjective : Function.Surjective ActualQJ318.jInvariant := by
  have he : Set.range ActualQJ318.jInvariant=Set.univ :=
    (show IsClopen (Set.range ActualQJ318.jInvariant) from ⟨range_isClosed,range_isOpen⟩).eq_univ
      (Set.range_nonempty _)
  exact Set.range_eq_univ.mp he

/-- Genuine j is onto on every already-defined fine-level quotient. -/
theorem quotient_surjective (N : ℕ) : Function.Surjective (QuotientJ318.jMap N) := by
  intro z
  obtain ⟨tau,htau⟩ := surjective z
  exact ⟨quotientMap N tau,htau⟩

/-- The actual all-cusp extension is onto the honest complex sphere. -/
theorem sphere_surjective (N : ℕ) (hN : 5≤N) : Function.Surjective (jInfinity N hN) := by
  change ∀z : OnePoint ℂ, ∃p, jInfinity N hN p=z
  refine OnePoint.forall.mpr ?_
  constructor
  · exact ⟨cusp N hN (Classical.arbitrary (FiniteCuspEnds318.End N)),jInfinity_cusp N hN _⟩
  · intro z
    obtain ⟨tau,htau⟩ := surjective z
    refine ⟨original N hN (quotientMap N tau),?_⟩
    rw [jInfinity_original,QuotientJ318.jMap_projection,htau]

end ActualJSurjective318
