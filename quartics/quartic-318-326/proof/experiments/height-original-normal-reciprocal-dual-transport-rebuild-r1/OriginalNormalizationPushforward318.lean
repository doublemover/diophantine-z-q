module
public import IntegralNormalizationDualPushforward318
public import OriginalNormalizationCounit318
public import OriginalNormalOrderChart318
public section
noncomputable section
namespace OriginalNormalizationPushforward318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "A" => IntegralDistinctContactOpen318.Source R a d
local notation "B" => SourceOpenRing c t w D
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "ν" => IntegralNormalizationFiniteMap318.map R a d

/-- The finite normalization map used by the sheaf pushforward is
produced on the ACTUAL original chart at every finite place. -/
theorem finite : IsFinite ν := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact IntegralNormalizationFiniteMap318.finite R a d (coefficients_ne_zero c t w D)

/-- Both paths begin with the identical original source inclusion into
normalOrder: one enters the SAME proper normal model M, the other is the
finite map to the raw order used in the native sheaf pushforward. -/
theorem actual_diagrams :
    (Spec.map (CommRingCat.ofHom N.val.toRingHom) ≫
      OriginalNormalOrderChart318.chart c t w D M=M.source) ∧
    (Spec.map (CommRingCat.ofHom N.val.toRingHom) ≫ ν=
      Spec.map (CommRingCat.ofHom
        (IntegralFourRootNormalizationConductor318.inclusion R a d).toRingHom)) :=
  ⟨OriginalNormalOrderChart318.source c t w D M,
    IntegralNormalizationFiniteMap318.source_square R a d⟩

/-- Native pushforward of the entire finite dual from this actual
normal chart is identified with the conductor sheaf, including bad primes.
This does NOT identify that affine dual with a global Hodge sheaf. -/
@[expose] def conductorIso : IntegralNormalizationDualPushforward318.pushed R a d ≅
    tilde (R:=CommRingCat.of A)
      (ModuleCat.of A (IntegralNormalizationConductorIdeal318.ideal R a d)) := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact IntegralNormalizationDualPushforward318.conductorIso R a d (coefficients_ne_zero c t w D)

/-- The underlying full module counit of this native sheaf map has
precisely the prior signed-point coefficient and proved cotangent bound.
No new point, generator, or scalar normalization enters the consumer. -/
theorem original_coefficient_bound (ht : w (t : K c t) ≤ 1)
    (f : OriginalNormalOrderFiniteDual318.Dual c t w D) :
    OriginalNormalizationCounit318.value c t w D M f=
      OriginalNormalizationDifferentValue318.differentValue c t w D M *
        OriginalNormalOrderFiniteDual318.value c t w D M f ∧
    OriginalNormalizationCounit318.value c t w D M f ∈
      OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M :=
  ⟨OriginalNormalizationCounit318.value_eq c t w D M f,
    OriginalNormalizationCounit318.value_mem c t w D M ht f⟩
end OriginalNormalizationPushforward318
