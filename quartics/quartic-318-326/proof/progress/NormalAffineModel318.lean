module
public import AffineIntegralModel318
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public section
noncomputable section
namespace NormalAffineModel318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
universe u
variable {R K B L:Type u} [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra R B]
  [Field L] [Algebra R L] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower R B L] [Algebra K L] [IsScalarTower R K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The actual integral model inside the open algebra is also the integral
closure in its genuine function field. -/
theorem model_integralClosure : IsIntegralClosure (integralClosure R B) R L :=
  IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn
    R (integralClosure R B) B L

include K L

/-- The normal affine model is genuinely finite by the proved trace-dual
integral-closure finiteness theorem. -/
theorem model_finite : Module.Finite R (integralClosure R B) := by
  let:=model_integralClosure (L:=L) (R:=R) (B:=B)
  exact IsIntegralClosure.finite R K L (integralClosure R B)

/-- Actual finite structure morphism of the integral-closure model. -/
theorem structure_finite : IsFinite (AffineIntegralModel318.structureMap (R:=R) (B:=B)) := by
  let:=model_finite (K:=K) (L:=L) (R:=R) (B:=B)
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- Properness is over the affine base, not a projective completion claim. -/
theorem structure_proper : IsProper (AffineIntegralModel318.structureMap (R:=R) (B:=B)) := by
  let:=structure_finite (K:=K) (L:=L) (R:=R) (B:=B)
  infer_instance

end NormalAffineModel318
