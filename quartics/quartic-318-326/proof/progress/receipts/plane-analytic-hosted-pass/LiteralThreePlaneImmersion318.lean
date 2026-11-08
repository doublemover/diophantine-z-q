module
public import LiteralThreePlanePoints318
public section
noncomputable section
namespace LiteralThreePlaneImmersion318
open Polynomial OpenJModel318 OpenJAffineScheme318 ArithmeticPointTopology318
open ModularCoordinateProper318 ModularArithmeticCoordinates318
open LiteralThreeBaseEvaluation318 LiteralThreePlanePoints318
set_option maxHeartbeats 0

@[expose] def partialX (z x : ℂ) : ℂ :=
  4*(z-1728)^2*x^3-12*z*(z-1728)*x-8*z*(z-1728)

lemma hasDerivAt_Q (z x : ℂ) : HasDerivAt (Q z) (partialX z x) x := by
  have h := (((((hasDerivAt_id x).pow 4).const_mul ((z-1728)^2)).sub
    (((hasDerivAt_id x).pow 2).const_mul (6*z*(z-1728)))).sub
      ((hasDerivAt_id x).const_mul (8*z*(z-1728)))).sub_const (3*z^2)
  convert h using 1
  · funext w
    rfl
  · simp only [partialX,Pi.pow_apply,id_eq]
    ring

/-- Exact derivative normalization for the literal arithmetic coefficients. -/
lemma partialX_factor (N : ℕ) [NeZero N] (z : JOpen) (x : ℂ) :
    partialX z.val x=4*(z.val-1728)^2*
      (x^3+evaluation N z (A N)*x+evaluation N z (B N)) := by
  rw [evaluation_A,evaluation_B]
  unfold partialX
  field_simp [sub_ne_zero.mpr z.property.2]
  <;> ring

/-- The genuine unit in the actual x-coordinate algebra remains nonzero
under every literal complex point. This is not inferred from a point count. -/
lemma point_cubic_ne_zero (N : ℕ) [NeZero N] (p : Points N) :
    (p.hom (xGenerator N))^3+evaluation N (jValue N p) (A N)*p.hom (xGenerator N)+
      evaluation N (jValue N p) (B N)≠0 := by
  letI : Algebra (Base N) ℂ := (evaluation N (jValue N p)).toAlgebra
  have h := ((ShortThreeTorsion318.cubic_unit (A N) (B N) (discriminant_unit N)).map
    (pointXHom N p).toRingHom).ne_zero
  change pointXHom N p (AdjoinRoot.mk (ShortThreeTorsion318.polynomial (A N) (B N))
    (ShortTwoTorsion318.polynomial (A N) (B N)))≠0 at h
  simpa only [ShortTwoTorsion318.polynomial,map_add,map_mul,map_pow,AdjoinRoot.mk_X,
    AdjoinRoot.mk_C,←AdjoinRoot.algebraMap_eq,AlgHom.commutes,pointXHom_root,
    RingHom.algebraMap_toAlgebra] using h

lemma point_partialX_ne_zero (N : ℕ) [NeZero N] (p : Points N) :
    partialX (jValue N p).val (p.hom (xGenerator N))≠0 := by
  rw [partialX_factor N]
  exact mul_ne_zero (mul_ne_zero (by norm_num : (4:ℂ)≠0)
    (pow_ne_zero 2 (sub_ne_zero.mpr (jValue N p).property.2))) (point_cubic_ne_zero N p)

/-- Every point of the literal open quartic has nonzero x partial derivative,
using the actual inverse algebra map rather than a supplied smoothness premise. -/
theorem plane_partialX_ne_zero (p : Plane) : partialX p.val.1.val p.val.2≠0 := by
  have h := point_partialX_ne_zero 1 (fromPlane 1 p)
  change partialX (pointCoordinates 1 (fromPlane 1 p)).1.val
    (pointCoordinates 1 (fromPlane 1 p)).2≠0 at h
  rw [fromPlane_coordinates] at h
  exact h

theorem plane_deriv_ne_zero (p : Plane) : deriv (Q p.val.1.val) p.val.2≠0 := by
  rw [(hasDerivAt_Q _ _).deriv]
  exact plane_partialX_ne_zero p

end LiteralThreePlaneImmersion318
