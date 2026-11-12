module
public import ActualOriginalQuadraticPolarization318
public import Mathlib.Algebra.BigOperators.Ring.Finset
public section
noncomputable section
namespace ActualOriginalWeightedWeylIdentity318
open QuadricCRTAssembly318 ActualOriginalQuadraticPolarization318
open ActualOriginalFiniteCircleIdentity318
open scoped BigOperators

/-- All actual displacements between original lattice points. In
particular this contains every pair used by the squared finite sum. -/
@[expose] def differences (s : Finset (Coordinates ℤ)) : Finset (Coordinates ℤ) := by
  classical
  exact (s.product s).image (fun xy => xy.1-xy.2)

/-- The correlation keeps the ORIGINAL weight at both original points.
The fiber condition does not replace either point by an independent one. -/
@[expose] def linearCorrelation (κ : ℤ) (s : Finset (Coordinates ℤ))
    (w : Coordinates ℤ → ℂ) (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) : ℂ := by
  classical
  exact ∑ xy ∈ (s.product s).filter (fun xy => xy.1-xy.2=h),
    w xy.1 * starRingEnd ℂ (w xy.2) * fourier (2*originalBilinear κ h xy.2) θ

/-- Weighted finite Weyl differencing on the SAME original five-variable
sum. This is an equality, not an assumption of cancellation. -/
theorem actual_original_weighted_weyl (κ : ℤ) (s : Finset (Coordinates ℤ))
    (w : Coordinates ℤ → ℂ) (θ : AddCircle (1 : ℝ)) :
    originalCircleSum κ s w θ * starRingEnd ℂ (originalCircleSum κ s w θ) =
      ∑ h ∈ differences s, fourier (equation κ h) θ * linearCorrelation κ s w θ h := by
  classical
  let f (xy : Coordinates ℤ × Coordinates ℤ) : ℂ :=
    (w xy.1*fourier (equation κ xy.1) θ)*
      starRingEnd ℂ (w xy.2*fourier (equation κ xy.2) θ)
  have hfiber :
      (∑ h ∈ differences s, ∑ xy ∈ (s.product s).filter (fun xy => xy.1-xy.2=h), f xy) =
        ∑ xy ∈ s.product s, f xy :=
    Finset.sum_fiberwise_of_maps_to
      (fun xy hxy => Finset.mem_image_of_mem (fun xy => xy.1-xy.2) hxy) _
  calc
    _ = ∑ xy ∈ s.product s, f xy := by
      simp only [originalCircleSum,Finset.sum_apply,map_sum,Finset.sum_mul,
        Finset.mul_sum,Finset.sum_product,f]
    _ = ∑ h ∈ differences s, ∑ xy ∈ (s.product s).filter (fun xy => xy.1-xy.2=h), f xy :=
      hfiber.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [linearCorrelation,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xy hxy
      have hd := (Finset.mem_filter.mp hxy).2
      dsimp only [f]
      rw [map_mul]
      calc
        _ = (w xy.1*starRingEnd ℂ (w xy.2))*
            (fourier (equation κ xy.1) θ*starRingEnd ℂ (fourier (equation κ xy.2) θ)) := by ring
        _ = _ := by rw [actual_original_phase_difference,hd]; ring

end ActualOriginalWeightedWeylIdentity318
