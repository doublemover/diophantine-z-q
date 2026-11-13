module
public import IntegralClosureFullDualLocalization318
public import IntegralNormalOverlapFiniteDual318
public import IntegralNormalOverlapInfinityDual318
public section
noncomputable section
namespace IntegralClosureDualRestrictionSeparation318
variable {P Q B : Type*} [CommRing P] [CommRing Q] [CommRing B]
  [Algebra P Q] [Algebra P B] [Algebra Q B] [IsScalarTower P Q B]
  (s : P) [IsLocalization.Away s Q]
local notation "N" => integralClosure P B
local notation "O" => integralClosure Q B
local notation "i" => IntegralClosureLocalizationMap318.inclusion (P:=P) (Q:=Q) (B:=B)
local instance : IsLocalizedModule (Submonoid.powers s) i.toLinearMap :=
  IntegralClosureModuleLocalization318.localization (Q:=Q) (B:=B) s

include s in
/-- All old integral inputs separate the entire localized Hom, not just
the marked root basis or an image submodule. -/
lemma ext {f g : O →ₗ[P] Q} (h : ∀ n : N,f (i n)=g (i n)) : f=g := by
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers s) i.toLinearMap
    (Algebra.linearMap P Q)
  exact LinearMap.ext h

include s in
lemma eq_iff (f g : O →ₗ[P] Q) : f=g ↔ ∀ n : N,f (i n)=g (i n) :=
  ⟨fun h n => congrArg (fun k : O →ₗ[P] Q => k (i n)) h,ext s⟩

/-- The native full-Hom extension has its exact multiplication
precomposition action on EVERY old normal-order element. -/
lemma multiplication (f : N →ₗ[P] P) (n m : N) :
    IntegralClosureFullDualLocalization318.map (Q:=Q) (B:=B) s f (i n*i m)=
      algebraMap P Q (f (n*m)) := by
  rw [←map_mul,IntegralClosureFullDualLocalization318.map_value]
end IntegralClosureDualRestrictionSeparation318

namespace OriginalNormalOverlapFullHom318
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

/-- The actual original finite-place normal order and overlap, retaining
the original normalized data rather than replacing it with a free model. -/
@[expose] def finiteEquivalence : S ⊗[P] (N →ₗ[P] P) ≃ₗ[S] (O →ₗ[P] S) := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact IntegralNormalOverlapFiniteDual318.equivalence R a d
    (coefficients_ne_zero c t w D)

section Infinity
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local notation "Ni" => IntegralInfinityNormalConductor318.normalOrder R a d
local notation "Oi" => IntegralOriginalNormalOverlap318.InfinityOverlap R a d

/-- Independent reciprocal polynomial scalar action at the SAME point.
No identification with the finite Hom or dT/dS transition is inserted. -/
@[expose] def infinityEquivalence : S ⊗[P] (Ni →ₗ[P] P) ≃ₗ[S] (Oi →ₗ[P] S) := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact IntegralNormalOverlapInfinityDual318.equivalence R a d
    (coefficients_ne_zero c t w D)
end Infinity
end OriginalNormalOverlapFullHom318
