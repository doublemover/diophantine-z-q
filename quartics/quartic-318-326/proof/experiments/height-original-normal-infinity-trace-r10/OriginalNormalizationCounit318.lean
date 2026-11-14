module
public import IntegralNormalizationCounitSheaf318
public import IntegralNormalizationConductorQuotient318
public import OriginalNormalOrderFiniteDual318
public section
noncomputable section
namespace OriginalNormalizationCounit318
open NumberField Polynomial
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "P" => Polynomial R
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "A" => IntegralDistinctContactOpen318.Source R a d
local notation "B" => SourceOpenRing c t w D
local notation "F" => IntegralDistinctContactOpen318.Base R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "inc" => IntegralFourRootNormalizationConductor318.inclusion R a d
local notation "into" => IntegralFourRootNormalizationConductor318.intoNormal R a d
local notation "δ" => OriginalNormalizationDifferentValue318.differentValue c t w D M
local notation "I" => IntegralNormalizationConductorIdeal318.ideal R a d

/-- Evaluate the ACTUAL raw coefficient of the normalization counit
at the unchanged signed original point. No new local point is chosen. -/
@[expose] def value (f : OriginalNormalOrderFiniteDual318.Dual c t w D) : K c t :=
  M.fieldPoint (inc (IntegralNormalizationCounit318.coordinate R a d f))

/-- The scalar comparing the raw dual coordinate to the original
normal-dual trace coordinate is exactly the same original raw different. -/
theorem value_eq (f : OriginalNormalOrderFiniteDual318.Dual c t w D) :
    value c t w D M f=δ*OriginalNormalOrderFiniteDual318.value c t w D M f := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  let E := IntegralNormalizationFiniteDual318.equivalence R a d (coefficients_ne_zero c t w D)
  have h := IntegralNormalizationCounit318.coefficient_formula R a d
    (coefficients_ne_zero c t w D) (E.symm f)
  rw [LinearEquiv.apply_symm_apply] at h
  change M.fieldPoint (inc (IntegralNormalizationCounit318.coordinate R a d f))=_
  rw [h,map_mul]
  rfl

/-- The actual normalization counit's original-point image is precisely
the prior conductor specialization, including every conductor element. -/
theorem value_range : Set.range (value c t w D M)=
    (OriginalNormalizationConductorSpecialization318.conductorValues c t w D M : Set (K c t)) := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  have hr := IntegralNormalizationConductorIdeal318.range_coordinate R a d
    (coefficients_ne_zero c t w D)
  ext y
  constructor
  · rintro ⟨f,rfl⟩
    have hc : IntegralNormalizationCounit318.coordinate R a d f ∈ I := by
      rw [←hr]
      exact ⟨f,rfl⟩
    exact ⟨inc (IntegralNormalizationCounit318.coordinate R a d f),hc,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨x,hx⟩ := (FiniteOrderConductorTraceDual318.mem_conductor inc N b).mp hb 1
    have hx' : inc x=b := by
      change inc x=b*1 at hx
      simpa only [mul_one] using hx
    have hi : x ∈ I := by change inc x ∈ _; rw [hx']; exact hb
    rw [←hr] at hi
    obtain ⟨f,hf⟩ := hi
    refine ⟨f,?_⟩
    change M.fieldPoint (inc (IntegralNormalizationCounit318.coordinate R a d f))=M.fieldPoint b
    rw [hf,hx']

/-- This is an actual normalization-counit bound at the SAME old
closed center, on the explicit finite-chart branch. The correction has
become the counit's coefficient; it is not discarded. -/
theorem value_mem (ht : w (t : K c t) ≤ 1) (f : OriginalNormalOrderFiniteDual318.Dual c t w D) :
    value c t w D M f ∈ OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M := by
  rw [value_eq]
  exact OriginalNormalOrderFiniteDual318.corrected_mem c t w D M ht f

theorem value_pairing (ht : w (t : K c t) ≤ 1)
    (f : OriginalNormalOrderFiniteDual318.Dual c t w D) (q : K c t)
    (hq : q ∈ OriginalNormalCenterDualImage318.dual c t w D M) :
    w (q*value c t w D M f) ≤ 1 := by
  rw [value_eq]
  exact OriginalNormalOrderFiniteDual318.corrected_pairing c t w D M ht f q hq
end OriginalNormalizationCounit318
