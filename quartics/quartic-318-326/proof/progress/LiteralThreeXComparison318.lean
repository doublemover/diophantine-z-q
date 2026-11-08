module
public import CanonicalXScale318
public import ThreeXAlgebraPoints318
public import ThreeTorsionSignQuotient318
public import LiteralThreeAnalyticComparison318
public section
noncomputable section
namespace LiteralThreeXComparison318
open OpenJComplexEvaluation318 OpenJModel318 OpenJAffineScheme318 ThreeTorsionAlgebra318
set_option maxHeartbeats 0

abbrev AnalyticRoots (tau : UpperHalfPlane) :=
  ThreeRootScaling318.Roots (ModularWeierstrass318.curve tau).a₄ (ModularWeierstrass318.curve tau).a₆

/-- Canonical complex-point comparison of the actual arithmetic quartic
x-algebra with the actual analytic third-division quartic. No square root
or arbitrary four-point labeling enters the map. -/
@[expose] def rootEquiv (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    (XRing (A N) (B N) →ₐ[Base N] ℂ) ≃ AnalyticRoots tau := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  have hA : algebraMap (Base N) ℂ (A N)=(fiber N tau h).a₄ := rfl
  have hB : algebraMap (Base N) ℂ (B N)=(fiber N tau h).a₆ := rfl
  have hc := CanonicalXScale318.coefficient_comparison N tau h
  exact (ThreeXAlgebraPoints318.rootEquiv (K:=ℂ) (A N) (B N)).trans
    (ThreeRootScaling318.rootEquiv _ _ _ _
      (Units.mk0 (CanonicalXScale318.scale (tau:ℂ)) (CanonicalXScale318.scale_ne_zero N tau h))
      (by simpa only [Units.val_mk0,hA] using hc.1)
      (by simpa only [Units.val_mk0,hB] using hc.2))

theorem rootEquiv_apply (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    ∀ f : XRing (A N) (B N) →ₐ[Base N] ℂ,
      (rootEquiv N tau h f).val = CanonicalXScale318.scale (tau:ℂ) *
        f (AdjoinRoot.root (ShortThreeTorsion318.polynomial (A N) (B N))) := by
  intro f
  rfl

abbrev Fixed (N : ℕ) [NeZero N] := ThreeTorsionSignQuotient318.Fixed
  (A N) (B N) (discriminant_unit N)

@[expose] def fixedHomEquiv (N : ℕ) [NeZero N] [Algebra (Base N) ℂ] :
    (Fixed N →ₐ[Base N] ℂ) ≃ (XRing (A N) (B N) →ₐ[Base N] ℂ) where
  toFun f := f.comp (ThreeTorsionSignQuotient318.signQuotientEquiv
    (A N) (B N) (discriminant_unit N)).toAlgHom
  invFun f := f.comp (ThreeTorsionSignQuotient318.signQuotientEquiv
    (A N) (B N) (discriminant_unit N)).symm.toAlgHom
  left_inv f := by
    apply AlgHom.ext
    intro x
    change f ((ThreeTorsionSignQuotient318.signQuotientEquiv (A N) (B N) (discriminant_unit N))
      ((ThreeTorsionSignQuotient318.signQuotientEquiv (A N) (B N) (discriminant_unit N)).symm x)) = f x
    rw [AlgEquiv.apply_symm_apply]
  right_inv f := by
    apply AlgHom.ext
    intro x
    change f ((ThreeTorsionSignQuotient318.signQuotientEquiv (A N) (B N) (discriminant_unit N)).symm
      ((ThreeTorsionSignQuotient318.signQuotientEquiv (A N) (B N) (discriminant_unit N)) x)) = f x
    rw [AlgEquiv.symm_apply_apply]

/-- The full diamond fixed algebra, canonically identified with the actual
rank-four x-algebra, has the same canonical analytic quartic comparison. -/
@[expose] def fixedRootEquiv (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    (Fixed N →ₐ[Base N] ℂ) ≃ AnalyticRoots tau := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  exact (fixedHomEquiv N).trans (rootEquiv N tau h)

end LiteralThreeXComparison318
