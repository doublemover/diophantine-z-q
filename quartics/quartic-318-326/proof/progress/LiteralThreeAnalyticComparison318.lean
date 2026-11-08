module
public import OpenJAnalyticPoints318
public import ThreeTorsionOrderEquiv318
public import LiteralThreeTorsion318
public section
noncomputable section
namespace LiteralThreeAnalyticComparison318
open OpenJComplexEvaluation318 OpenJModel318 OpenJAffineScheme318
set_option maxHeartbeats 0

@[expose] def exactOrderCongr {K : Type*} [Field K] [DecidableEq K]
    {W W' : WeierstrassCurve K} (he : W=W') (n : ℕ) :
    {P : W.toAffine.Point // addOrderOf P=n} ≃ {P : W'.toAffine.Point // addOrderOf P=n} := by
  subst W'
  exact Equiv.refl _

lemma literal_curve_eq (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    ThreeTorsionOrderEquiv318.Curve (K:=ℂ) (A N) (B N) = fiber N tau h := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  ext <;> simp only [ThreeTorsionOrderEquiv318.Curve, ThreeTorsionPoints318.curve,
    TwoTorsionPoints318.curve, fiber, integralModel, OpenJModel318.curve, A, B,
    WeierstrassCurve.map, map_zero]
  all_goals rfl


/-- The actual complex fiber of the rank-eight finite-etale algebra is
identified with genuine primitive order-three period vectors. The only
choice is the already-constructed complex coordinate scaling. -/
@[expose] def primitiveEquiv (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    (LiteralThreeTorsion318.Ring N →ₐ[Base N] ℂ) ≃
      {v : ZMod 3 × ZMod 3 // PrimitiveTorsion318.Primitive 3 v} := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  exact ((ThreeTorsionOrderEquiv318.algebraPointEquiv (K:=ℂ) (A N) (B N)
    (discriminant_unit N)).trans (exactOrderCongr (literal_curve_eq N tau h) 3)).trans
      (OpenJAnalyticPoints318.primitiveEquiv N tau h 3).symm

/-- In particular, these are eight actual geometric points of the specified
arithmetic family, now matched with analytic periods rather than arbitrary labels. -/
theorem nonempty_complex_fiber (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    Nonempty (LiteralThreeTorsion318.Ring N →ₐ[Base N] ℂ) := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  refine ⟨(primitiveEquiv N tau h).symm ⟨(0,1), ?_⟩⟩
  norm_num [PrimitiveTorsion318.Primitive,ZMod.val_one_eq_one_mod]

end LiteralThreeAnalyticComparison318
