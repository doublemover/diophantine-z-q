module
public import PELOriginalFixedKleinCoordinates318
public import PELIntegralEllipticObstructions318
public section
noncomputable section
namespace PELOriginalFixedIntegralCoordinates318
open PELPrincipalOrderCoordinates318 PELLevelThreeSimilitudes318
open PELIntegralEllipticObstructions318 PELQuaternionRealRepresentation318
open PELOriginalFixedKleinCoordinates318 QuaternionicFixedParameter318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
set_option maxHeartbeats 2400000

@[expose] def rotationCoordinate (x : Coordinates) : ℤ := 2*x 1+x 3

/-- These are coordinates in the original maximal-order basis, with no
change to the real representation or the quaternionic polarization. -/
theorem original_matrix (x : Coordinates) (ht : trace x=0) :
    representation (embed x)=
      traceZeroMatrix (x 0:ℝ) (rotationCoordinate x:ℝ) (x 3:ℝ) := by
  have h2 : x 2= -2*x 0 := by unfold trace at ht; omega
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [representation,matrix,embed,traceZeroMatrix,rotationCoordinate,h2] <;>
    push_cast <;> ring

theorem norm_equation (x : Coordinates) (ht : trace x=0) :
    105*(rotationCoordinate x)^2-10*(x 0)^2-21*(x 3)^2=2*integralNorm x := by
  have h2 : x 2= -2*x 0 := by unfold trace at ht; omega
  simp only [rotationCoordinate,integralNorm,h2]
  ring

/-- A complete source-to-finite-arithmetic interface for any original
integral trace-zero element fixing an upper-half-plane point. -/
theorem original_fixed_coordinates (x : Coordinates) (ht : trace x=0)
    (hn : 0<integralNorm x) (τ : HalfPlane)
    (hfix : fixesLine (representation (embed x)) τ) :
    rotationCoordinate x≠0 ∧
    scaledFirst τ= -10*(x 0:ℝ)/(rotationCoordinate x:ℝ) ∧
    scaledSecond τ= -(x 3:ℝ)/(rotationCoordinate x:ℝ) ∧
    (integralNorm x:ℝ)*(height τ)^2=210*(rotationCoordinate x:ℝ)^2 := by
  have he := norm_equation x ht
  have hr : rotationCoordinate x≠0 := by
    intro hz; rw [hz] at he; nlinarith [sq_nonneg (x 0),sq_nonneg (x 3)]
  have hrR : (rotationCoordinate x:ℝ)≠0 := by exact_mod_cast hr
  have heR : 105*(rotationCoordinate x:ℝ)^2-10*(x 0:ℝ)^2-21*(x 3:ℝ)^2=
      2*(integralNorm x:ℝ) := by exact_mod_cast he
  rw [original_matrix x ht] at hfix
  obtain ⟨hf,hs⟩ := fixed_coordinates _ _ _ τ hrR hfix
  exact ⟨hr,hf,hs,fixed_height_square _ _ _ _ τ heR hrR hfix⟩

theorem original_fixed_bound (x : Coordinates) (ht : trace x=0)
    (hn : 0<integralNorm x) (τ : HalfPlane)
    (hfix : fixesLine (representation (embed x)) τ) (hh : height τ≤200) :
    210*(rotationCoordinate x)^2≤40000*integralNorm x := by
  have heR : 105*(rotationCoordinate x:ℝ)^2-10*(x 0:ℝ)^2-21*(x 3:ℝ)^2=
      2*(integralNorm x:ℝ) := by exact_mod_cast norm_equation x ht
  have hnR : 0<(integralNorm x:ℝ) := by exact_mod_cast hn
  rw [original_matrix x ht] at hfix
  exact_mod_cast bounded_original_coordinate _ _ _ _ τ heR hnR hfix hh
end PELOriginalFixedIntegralCoordinates318
