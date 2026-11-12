module
public import IntegralNormalSourceDifferentialFrame318
public import OriginalNormalCenterAffineChart318
public section
noncomputable section
namespace OriginalNormalSourceCotangent318
open Polynomial NumberField CategoryTheory AlgebraicGeometry
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPlaceNormalModel318 IntegralDistinctContactOpen318
set_option maxHeartbeats 1000000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local instance : Algebra (SourceOpenRing c t w D) (K c t) := M.fieldPoint.toAlgebra

/-- The actual generic cotangent at the very same original field point
used by the proper normal-model center. Not the cotangent of its point field. -/
abbrev Fiber := FramedCotangentFiber318.Fiber (V c t w) (SourceOpenRing c t w D) (K c t)

@[expose] def frame : Fiber c t w D M ≃ₗ[K c t] K c t :=
  FramedCotangentFiber318.frame _ _ _
    (IntegralNormalSourceDifferentialFrame318.frame (V c t w) (contacts c t w) D.coefficients)

@[expose] def dt : Fiber c t w D M :=
  FramedCotangentFiber318.differential _ _ _
    (IntegralNormalSourceDifferentialFrame318.coordinate (V c t w) (contacts c t w) D.coefficients)

theorem frame_dt : frame c t w D M (dt c t w D M) = 1 := by
  rw [frame,dt,FramedCotangentFiber318.frame_differential,
    IntegralNormalSourceDifferentialFrame318.frame_D,map_one]

/-- The explicit frame proves this original generic cotangent direction
is nonzero. It does not assert a rank for an unidentified special fiber. -/
theorem dt_ne_zero : dt c t w D M ≠ 0 := by
  intro h
  have hh := frame_dt c t w D M
  rw [h,map_zero] at hh
  exact zero_ne_one hh

/-- Every actual cotangent vector is a unique coefficient times the
specified original dt vector; the identification is not just abstract rank one. -/
theorem unique_dt_coefficient (ω : Fiber c t w D M) :
    ∃! q : K c t, q • dt c t w D M = ω := by
  refine ⟨frame c t w D M ω,?_,?_⟩
  · apply (frame c t w D M).injective
    rw [map_smul,frame_dt,smul_eq_mul,mul_one]
  · intro q hq
    have h := congrArg (frame c t w D M) hq
    simpa only [map_smul,frame_dt,smul_eq_mul,mul_one] using h

theorem field_scalar (r : V c t w) :
    M.fieldPoint (algebraMap (V c t w) (SourceOpenRing c t w D) r) =
      algebraMap (V c t w) (K c t) r := by
  have h := M.field_polynomial (C r)
  rw [IntegralReciprocalBase318.finite_C,
    ←IsScalarTower.algebraMap_apply (V c t w) (Base (V c t w) (contacts c t w) D.coefficients)
      (SourceOpenRing c t w D)] at h
  simpa only [Polynomial.aeval_C] using h

theorem original_coordinate : M.fieldPoint
    (IntegralNormalSourceDifferentialFrame318.coordinate (V c t w)
      (contacts c t w) D.coefficients) = (t : K c t) := by
  simpa only [IntegralNormalSourceDifferentialFrame318.coordinate,Polynomial.aeval_X]
    using M.field_polynomial X

@[expose] def rootDifferential (i : Fin 4) : Fiber c t w D M :=
  FramedCotangentFiber318.differential _ _ _
    (IntegralNormalSourceDifferentialFrame318.root (V c t w) (contacts c t w) D.coefficients i)

/-- No nonzero-root premise or division is inserted: the undivided
identity holds in the exact original normalized generic fiber. -/
theorem normalized_root_relation (i : Fin 4) :
    2 * D.normalizedRoots i * frame c t w D M (rootDifferential c t w D M i) =
      algebraMap (V c t w) (K c t) (D.coefficients i) := by
  rw [frame,rootDifferential,FramedCotangentFiber318.frame_differential]
  change 2 * D.normalizedRoots i * M.fieldPoint _ = _
  have h := congrArg M.fieldPoint
    (IntegralNormalSourceDifferentialFrame318.root_differential
      (V c t w) (contacts c t w) D.coefficients i)
  simp only [map_mul,map_ofNat,IntegralNormalSourceDifferentialFrame318.root,
    M.field_roots,field_scalar] at h
  exact h

/-- Undo the actual normalization scalar on the actual cotangent vector,
retaining the original signed root, not merely its squareclass. -/
@[expose] def originalRootDifferential (i : Fin 4) : Fiber c t w D M :=
  D.multiplier i • rootDifferential c t w D M i

theorem original_signed_root_relation (i : Fin 4) :
    2 * RationalContactPoint318.sourcePoint c t
      (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i) *
        frame c t w D M (originalRootDifferential c t w D M i) =
      (fieldTwists c t i : K c t) := by
  rw [originalRootDifferential,map_smul,smul_eq_mul,←D.original_signed_root i]
  calc
    2 * (D.multiplier i * D.normalizedRoots i) *
        (D.multiplier i * frame c t w D M (rootDifferential c t w D M i)) =
        (D.multiplier i)^2 * (2 * D.normalizedRoots i *
          frame c t w D M (rootDifferential c t w D M i)) := by ring
    _ = (D.multiplier i)^2 * algebraMap (V c t w) (K c t) (D.coefficients i) := by
      rw [normalized_root_relation]
    _ = (fieldTwists c t i : K c t) := by
      rw [D.original_coefficient]
      change (D.multiplier i)^2 * algebraMap (V c t w) (K c t) (D.coefficients i) =
        algebraMap (V c t w) (K c t) (D.coefficients i) * (D.multiplier i)^2
      exact mul_comm _ _

/-- The coefficient is recovered on the same signed root, with its
actual sign and twist. Nonvanishing follows from the proved relation and
original twist unit, not from an assumed squareclass or a generic rank claim. -/
theorem original_signed_root_coefficient (i : Fin 4) :
    frame c t w D M (originalRootDifferential c t w D M i) =
      (fieldTwists c t i : K c t) /
        (2 * RationalContactPoint318.sourcePoint c t
          (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i)) := by
  have h := original_signed_root_relation c t w D M i
  have hn : 2 * RationalContactPoint318.sourcePoint c t
      (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i) ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at h
    exact (fieldTwists c t i).ne_zero h.symm
  apply (eq_div_iff hn).mpr
  rw [mul_comm]
  exact h

/-- The point underlying this frame is the original generic restriction
of the same integral center. The normal-center image still requires a
cotangent comparison across these actual chart maps. -/
theorem same_normal_center :
    Spec.map (CommRingCat.ofHom (algebraMap (V c t w) (K c t))) ≫ M.center =
      Spec.map (CommRingCat.ofHom M.fieldPoint) ≫ M.source := M.center_generic
end OriginalNormalSourceCotangent318
