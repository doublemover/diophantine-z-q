module
public import IntegralNormalizationFiniteDual318
public import OriginalCotangentDifferentBound318
public section
noncomputable section
namespace OriginalNormalOrderFiniteDual318
open NumberField Polynomial
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "P" => Polynomial R
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D
local notation "F" => IntegralDistinctContactOpen318.Base R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
abbrev Dual := FiniteDualModuleAction318.Dual P N

/-- The actual trace coefficient of EVERY finite dual functional on the
normal-order chart of the SAME model, not a selected generic frame. -/
@[expose] def coefficient (f : Dual c t w D) : B := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact ((IntegralNormalizationFiniteDual318.equivalence R a d
    (coefficients_ne_zero c t w D)).symm f).val

lemma coefficient_mem (f : Dual c t w D) : coefficient c t w D f ∈
    IntegralFourRootNormalizationConductor318.codifferent R a d := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact ((IntegralNormalizationFiniteDual318.equivalence R a d
    (coefficients_ne_zero c t w D)).symm f).property

/-- Literal trace realization on every normal-order section. The
normalization ring was already identified with the actual same-center
finite chart; no alternate ring or polynomial scalar is used here. -/
lemma trace_value (f : Dual c t w D) (n : N) :
    algebraMap P F (FiniteDualModuleAction318.evaluate P N f n)=
      Algebra.trace F B (coefficient c t w D f*n.val) := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  have h := IntegralNormalizationFiniteDual318.trace_value R a d
    (coefficients_ne_zero c t w D)
    ((IntegralNormalizationFiniteDual318.equivalence R a d
      (coefficients_ne_zero c t w D)).symm f) n
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

@[expose] def value (f : Dual c t w D) : K c t := M.fieldPoint (coefficient c t w D f)

lemma value_mem (f : Dual c t w D) : value c t w D M f ∈
    OriginalNormalizationConductorSpecialization318.codifferentValues c t w D M :=
  ⟨coefficient c t w D f,coefficient_mem c t w D f,rfl⟩

/-- The original specialized codifferent image is EXACTLY the values
of all finite-dual functionals on this actual chart, not just an upper
bound containing those values. -/
theorem value_range : Set.range (value c t w D M) =
    (OriginalNormalizationConductorSpecialization318.codifferentValues c t w D M :
      Set (K c t)) := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  ext y
  constructor
  · rintro ⟨f,rfl⟩
    exact value_mem c t w D M f
  · rintro ⟨z,hz,rfl⟩
    let zc : NormalTraceDualModule318.lattice (F:=F) N := ⟨z,hz⟩
    refine ⟨IntegralNormalizationFiniteDual318.equivalence R a d
      (coefficients_ne_zero c t w D) zc,?_⟩
    change M.fieldPoint
      (((IntegralNormalizationFiniteDual318.equivalence R a d
        (coefficients_ne_zero c t w D)).symm
        (IntegralNormalizationFiniteDual318.equivalence R a d
          (coefficients_ne_zero c t w D) zc)).val)=M.fieldPoint z
    rw [LinearEquiv.symm_apply_apply]
    rfl

/-- Every actual affine finite-dual value satisfies the proved
raw-different-corrected cotangent inclusion at the unchanged closed center.
This is not an identification with global Hodge or a regular-model lattice. -/
theorem corrected_mem (ht : w (t : K c t) ≤ 1) (f : Dual c t w D) :
    OriginalNormalizationDifferentValue318.differentValue c t w D M * value c t w D M f ∈
      OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M :=
  OriginalCotangentDifferentBound318.different_mul_mem c t w D M ht _ (value_mem c t w D M f)

theorem corrected_pairing (ht : w (t : K c t) ≤ 1) (f : Dual c t w D)
    (q : K c t) (hq : q ∈ OriginalNormalCenterDualImage318.dual c t w D M) :
    w (q*(OriginalNormalizationDifferentValue318.differentValue c t w D M * value c t w D M f)) ≤ 1 :=
  OriginalCotangentDifferentBound318.corrected_pairing c t w D M ht _
    (value_mem c t w D M f) q hq
end OriginalNormalOrderFiniteDual318
