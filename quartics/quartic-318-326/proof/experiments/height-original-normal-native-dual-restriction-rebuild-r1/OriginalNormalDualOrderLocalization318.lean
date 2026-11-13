module
public import IntegralNormalFiniteDualOrder318
public import IntegralNormalInfinityDualOrder318
public section
noncomputable section
namespace OriginalNormalDualOrderLocalization318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPlaceNormalModel318 Polynomial
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w)
local notation "R" => V c t w
local notation "P" => Polynomial R
local notation "S" => LaurentCoordinateInversion318.Base R
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "O" => IntegralOriginalNormalOverlap318.FiniteOverlap R a d
local instance : Algebra N O := OriginalNormalOverlapOrderLocalization318.finiteNormalAlgebra R a d
local instance : Module N (N →ₗ[P] P) := ValuedDualPrecomposition318.actionModule P N P
local instance : Module O (O →ₗ[P] S) := ValuedDualPrecomposition318.actionModule P O S

/-- Entire finite normal-order dual at the exact original finite place,
not a substitute free lattice. The returned map has the precomposition action. -/
@[expose] def finiteEquivalence :
    O ⊗[N] (N →ₗ[P] P) ≃ₗ[O] (O →ₗ[P] S) := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact IntegralNormalFiniteDualOrder318.equivalence R a d
    (coefficients_ne_zero c t w D)

section Infinity
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local notation "Ni" => IntegralInfinityNormalConductor318.normalOrder R a d
local notation "Oi" => IntegralOriginalNormalOverlap318.InfinityOverlap R a d
local instance : Algebra Ni Oi := OriginalNormalOverlapOrderLocalization318.infinityNormalAlgebra R a d
local instance : Module Ni (Ni →ₗ[P] P) := ValuedDualPrecomposition318.actionModule P Ni P
local instance : Module Oi (Oi →ₗ[P] S) := ValuedDualPrecomposition318.actionModule P Oi S

/-- Independently constructed reciprocal normal-order dual, retaining
the old inverse-coordinate scalar action at the SAME original point. -/
@[expose] def infinityEquivalence :
    Oi ⊗[Ni] (Ni →ₗ[P] P) ≃ₗ[Oi] (Oi →ₗ[P] S) := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact IntegralNormalInfinityDualOrder318.equivalence R a d
    (coefficients_ne_zero c t w D)
end Infinity
end OriginalNormalDualOrderLocalization318
