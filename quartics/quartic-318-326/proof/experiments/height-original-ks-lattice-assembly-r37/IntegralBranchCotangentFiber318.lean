module
public import CotangentParameterComparison318
public import OriginalSectionFinitePlaceBounds318
public section
noncomputable section
namespace IntegralBranchCotangentFiber318
open scoped TensorProduct
open IntegralBranchCoordinates318 IntegralBranchLocalization318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ) (i : Fin 4)
  (h2 : IsUnit (2:R)) (K : Type*) [Field K] (φ : B R c i →+* K)
local instance evaluationAlgebra : Algebra (B R c i) K := φ.toAlgebra
abbrev Fiber := FramedCotangentFiber318.Fiber R (B R c i) K
@[expose] def frame : Fiber R c i K φ ≃ₗ[K] K :=
  FramedCotangentFiber318.frame R (B R c i) K (sourceFrame R c i h2)
@[expose] def dt : Fiber R c i K φ :=
  FramedCotangentFiber318.differential R (B R c i) K (sourceT R c i)
@[expose] def coordinate : Fiber R c i K φ :=
  FramedCotangentFiber318.differential R (B R c i) K (sourceCoordinate R c i)

theorem coordinate_value : frame R c i h2 K φ (coordinate R c i K φ)=1 := by
  rw [frame,coordinate,FramedCotangentFiber318.frame_differential,source_normalized,map_one]

theorem dt_value : frame R c i h2 K φ (dt R c i K φ)=
    φ (2*algebraMap R (B R c i) (↑(c i)⁻¹:R)*sourceCoordinate R c i) := by
  rw [frame,dt,FramedCotangentFiber318.frame_differential,frame_D_sourceT]
  all_goals rfl

/-- Nonvanishing of Dt is derived from the actual coefficient identity on
the specified point's whole branch chart. No guessed root scale is used. -/
theorem dt_ne (hP : φ (IntegralBranchBicanonical318.sourceP R c i)≠0) :
    frame R c i h2 K φ (dt R c i K φ)≠0 := by
  have h := congrArg φ (IntegralBranchBicanonical318.cleared_frame R c i h2)
  simp only [map_mul,map_pow] at h
  have hc := ((IntegralBranchBicanonical318.coefficient0_unit R c i h2).map φ).ne_zero
  intro hz
  have hz' : φ (sourceFrame R c i h2 (KaehlerDifferential.D R (B R c i) (sourceT R c i)))=0 := by
    simpa only [frame,dt,FramedCotangentFiber318.frame_differential] using hz
  rw [hz',zero_pow (by decide : (2:ℕ)≠0)] at h
  exact mul_ne_zero hP hc h

/-- Literal original global J² coefficients specialized in the actual
squared cotangent fiber, rather than a pair of field scalars chosen by ratio. -/
@[expose] def section (n : Fin 2) : FramedCotangentFiber318.Square R (B R c i) K :=
  FramedCotangentFiber318.weighted R (B R c i) K
    (IntegralGlobalBicanonicalPair318.branchCoefficient R c i n) (sourceCoordinate R c i)

theorem section_value (n : Fin 2) :
    FramedCotangentFiber318.squareFrame R (B R c i) K (sourceFrame R c i h2)
      (section R c i K φ n)=φ (IntegralGlobalBicanonicalPair318.branchCoefficient R c i n) :=
  FramedCotangentFiber318.weighted_value _ _ _ _ _ _ (source_normalized R c i h2)

/-- The actual fiber of q0 is normalized by the original Dt square with
its exact J² factor. This supplies the differential, not just projective,
normalization needed for comparison with the original rational point. -/
theorem cleared_section :
    φ (IntegralBranchBicanonical318.sourceP R c i)*
      φ (IntegralGlobalBicanonicalPair318.branchCoefficient R c i 0)=
        (VerticalSection318.J:K)^2*(frame R c i h2 K φ (dt R c i K φ))^2 := by
  have h := congrArg φ (IntegralBranchBicanonical318.cleared_frame R c i h2)
  simp only [map_mul,map_pow] at h
  rw [IntegralGlobalBicanonicalPair318.branchCoefficient,if_pos rfl,map_mul,map_pow,map_intCast]
  rw [frame,dt,FramedCotangentFiber318.frame_differential]
  change _= (VerticalSection318.J:K)^2*(φ _)^2
  calc
    _ = (VerticalSection318.J:K)^2*(φ (IntegralBranchBicanonical318.sourceP R c i)*
      φ (IntegralBranchBicanonical318.coefficient0 R c i)) := by ring
    _ = _ := by rw [h]
end IntegralBranchCotangentFiber318
