module
public import IntrinsicHodgeIsomorphism318
public section
noncomputable section
namespace LiteralIntrinsicHodge318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Literal open-j base is a domain for nonzero level. -/
theorem base_domain (N : ℕ) (hN : N ≠ 0) : IsDomain (OpenJModel318.Base N) := by
  apply Localization.Away.isDomain
  unfold OpenJModel318.denominator
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) Polynomial.X_ne_zero) ?_
  · norm_num
  · exact Nat.cast_ne_zero.mpr hN
  · simpa using (Polynomial.X_sub_C_ne_zero (1728:ℤ))

/-- The actual global relative differential frame on the literal open-j family. -/
@[expose] def differentialFrame (N : ℕ) :
    FamilyIntrinsicDifferentials318.familyOmega (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≅
      GlobalInvariantLine318.line (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) :=
  IntrinsicGlobalFrame318.frame _ _ (OpenJAffineScheme318.discriminant_unit N)

theorem hodgeToIdentity_isIso (N : ℕ) (hN : N ≠ 0) :
    IsIso (IntrinsicHodgeComparison318.hodgeToIdentity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) := by
  letI := base_domain N hN
  exact IntrinsicHodgeIsomorphism318.hodgeToIdentity_isIso _ _ (OpenJAffineScheme318.discriminant_unit N)

@[expose] def hodgeToIdentityIso (N : ℕ) (hN : N ≠ 0) :
    IntrinsicHodgeComparison318.hodge (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≅
      IntrinsicHodgeComparison318.identityCotangent (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) := by
  letI := hodgeToIdentity_isIso N hN
  exact asIso (IntrinsicHodgeComparison318.hodgeToIdentity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))

@[expose] def hodgeFrame (N : ℕ) (hN : N ≠ 0) :
    IntrinsicHodgeComparison318.hodge (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≅
      SheafOfModules.unit (OpenJAffineScheme318.baseScheme N).ringCatSheaf :=
  hodgeToIdentityIso N hN ≪≫ IntrinsicIdentityFrame318.literalFrame N
end LiteralIntrinsicHodge318
