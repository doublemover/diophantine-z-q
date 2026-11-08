module
public import ThreeXComplexAlgebra318
public section
noncomputable section
namespace ThreeXComplexGeometry318
open ThreeXComplexAlgebra318 OpenJModel318 OpenJAffineScheme318 OpenJComplexEvaluation318
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
set_option maxHeartbeats 0

/-- Exact coordinate compatibility of the actual scalar-extension isomorphism.
The arithmetic x-coordinate is the analytic coordinate divided by the
canonical, sign-independent x-scale. -/
theorem xAlgebraEquiv_root (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    xAlgebraEquiv N tau h (1 ⊗ₜ[Base N] AdjoinRoot.root
      (ShortThreeTorsion318.polynomial (A N) (B N))) =
        algebraMap ℂ (AnalyticRing tau) ((CanonicalXScale318.scale (tau:ℂ))⁻¹) *
          AdjoinRoot.root (ShortThreeTorsion318.polynomial
            (ModularWeierstrass318.curve tau).a₄ (ModularWeierstrass318.curve tau).a₆) := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  simp only [xAlgebraEquiv,AlgEquiv.trans_apply,MonogenicSplitEquiv318.baseChange_root,
    AdjoinRoot.algEquivOfEq_root,ThreeXScalingAlgebra318.algebraEquiv_symm_root,
    map_mul,AlgEquiv.commutes,Units.val_inv_eq_inv_val]
  rfl

/-- The corresponding exact morphism on the literal full fixed algebra's
coordinate generator, using its proved inclusion into the eight-point algebra. -/
theorem fixedAlgebraEquiv_root (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    fixedAlgebraEquiv N tau h (1 ⊗ₜ[Base N]
      ThreeTorsionSignQuotient318.signQuotientEquiv (A N) (B N) (discriminant_unit N)
        (AdjoinRoot.root (ShortThreeTorsion318.polynomial (A N) (B N)))) =
        algebraMap ℂ (AnalyticRing tau) ((CanonicalXScale318.scale (tau:ℂ))⁻¹) *
          AdjoinRoot.root (ShortThreeTorsion318.polynomial
            (ModularWeierstrass318.curve tau).a₄ (ModularWeierstrass318.curve tau).a₆) := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  simpa [fixedAlgebraEquiv] using xAlgebraEquiv_root N tau h

/-- An actual isomorphism of complex affine schemes after scalar extension
of the specified arithmetic fixed algebra. This is not merely a bijection
of complex points, nor a claimed global moduli/analytification theorem. -/
@[expose] def fixedSchemeIso (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    Spec (CommRingCat.of (ℂ ⊗[Base N] LiteralThreeXComparison318.Fixed N)) ≅
      Spec (CommRingCat.of (AnalyticRing tau)) := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  exact Scheme.Spec.mapIso (fixedAlgebraEquiv N tau h).toRingEquiv.toCommRingCatIso.symm.op

end ThreeXComplexGeometry318
