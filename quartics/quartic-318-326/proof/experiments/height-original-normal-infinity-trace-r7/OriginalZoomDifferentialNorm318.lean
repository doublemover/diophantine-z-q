module
public import OriginalZoomDifferentialFrameScalar318
public import OriginalAllPrimeConstructedMetric318
public section
noncomputable section
namespace OriginalZoomDifferentialNorm318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j,RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
  (w : FinitePlace (K c t)) (D : Data c t w)
  {m : OriginalAllPrimeZoomInput318.Mode} (I : OriginalAllPrimeZoomInput318.Input c t w D m)

/-- The norm is the square of the ACTUAL evaluated differential change.
No replacement of this scalar by a unit or by a claimed global KS value. -/
theorem norm_identity : (w (OriginalZoomFiberLattice318.generator c t hn i w D I))⁻¹=
    (w (OriginalZoomDifferentialFrameScalar318.scalar c t w D I i))^2 := by
  rw [OriginalZoomDifferentialFrameScalar318.generator_eq_inverse_square c t hn w D I i,
    map_pow,map_inv₀,inv_pow,inv_inv]

theorem actual_frame_bound (n : Fin 2) :
    w (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)*
        (w (OriginalZoomDifferentialFrameScalar318.scalar c t w D I i))^2≤1 := by
  rw [←norm_identity c t hn i w D I]
  exact OriginalZoomFiberLattice318.original_norm_bound c t hn i w D I n

variable (u v : ℤ) (hf : ∀ j : Fin 5,ContactRadical318.forms u v j≠0)
/-- Exact norm formula at every excluded finite place of the produced
original per-(u,v) field, with its original branch and actual signed point. -/
theorem excluded_norm
    (b : OriginalExcludedPlaceData318.BadPlace c (OriginalContactAllPrimeNeighborhood318.coordinate u v)) :
    OriginalExcludedPlaceData318.excludedNorm c (OriginalContactAllPrimeNeighborhood318.coordinate u v)
      (RationalContactPoint318.parameters_ne_of_forms c u v hf) i
      (OriginalConstructedExcludedGenerators318.generators c u v hf i) b=
      (b.val (OriginalZoomDifferentialFrameScalar318.scalar c
        (OriginalContactAllPrimeNeighborhood318.coordinate u v) b.val
        (OriginalContactAllPrimeNeighborhood318.data c u v b.val)
        (OriginalContactAllPrimeNeighborhood318.input c u v hf b.val) i))^2 :=
  norm_identity c (OriginalContactAllPrimeNeighborhood318.coordinate u v)
    (RationalContactPoint318.parameters_ne_of_forms c u v hf) i b.val
    (OriginalContactAllPrimeNeighborhood318.data c u v b.val)
    (OriginalContactAllPrimeNeighborhood318.input c u v hf b.val)
end OriginalZoomDifferentialNorm318
