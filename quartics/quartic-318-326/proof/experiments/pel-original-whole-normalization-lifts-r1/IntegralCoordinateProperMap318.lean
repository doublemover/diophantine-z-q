module
public import IntegralCoordinateGrowth318
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace
public section
noncomputable section
namespace IntegralCoordinateProperMap318
open Set Metric
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A closed affine complex model with a genuine polynomial bound on
ALL coordinates has a proper original base projection. Compactness is
proved in the ordinary finite-dimensional Euclidean topology. -/
theorem proper_of_bound (S : Set (ι → ℂ)) (hS : IsClosed S)
    (π : (ι → ℂ) → (κ → ℂ)) (hπ : Continuous π)
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hb : ∀ w ∈ S, ‖w‖ ≤ C*(1+‖π w‖)^N+1) :
    IsProperMap (fun w : S => π w.val) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hπ.comp continuous_subtype_val,?_⟩
  intro K hK
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.exists_pos_norm_le
  let B := C*(1+R)^N+1
  have hJ : IsCompact (S ∩ π ⁻¹' K) := by
    apply (isCompact_closedBall (0 : ι → ℂ) B).of_isClosed_subset
      (hS.inter (hK.isClosed.preimage hπ))
    intro w hw
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (hb w hw.1).trans (add_le_add_right
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (add_le_add_left (hKR _ hw.2) 1) N) hC) 1)
  rw [Subtype.isCompact_iff]
  have he : (Subtype.val '' ((fun w : S => π w.val) ⁻¹' K)) = S ∩ π ⁻¹' K := by
    ext w
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.property,hw⟩
    · rintro ⟨hw,hπw⟩
      exact ⟨⟨w,hw⟩,hπw,rfl⟩
  rw [he]
  exact hJ

/-- Properness is PRODUCED from literal monic integral equations for
every source coordinate over the same base projection. Neither proper
complex analytification nor an algebraic-to-topological theorem is assumed. -/
theorem proper_of_monic_coordinates (S : Set (ι → ℂ)) (hS : IsClosed S)
    (π : (ι → ℂ) → (κ → ℂ)) (hπ : Continuous π)
    (Q : ι → Polynomial (MvPolynomial κ ℂ)) (hm : ∀ i, (Q i).Monic)
    (hroot : ∀ w ∈ S, ∀ i, ((Q i).map (MvPolynomial.eval (π w))).IsRoot (w i)) :
    IsProperMap (fun w : S => π w.val) := by
  obtain ⟨C,hC,N,hb⟩ := IntegralCoordinateGrowth318.exists_bound Q hm
  exact proper_of_bound S hS π hπ C hC N (fun w hw => hb (π w) w (hroot w hw))
end IntegralCoordinateProperMap318
