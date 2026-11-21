module
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public section
noncomputable section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace SelectedActualNumberFieldPlaceTrait318

variable {L : Type*} [Field L] [NumberField L]

/-- The actual ring of the original arithmetic trait. Its coefficients
map to the same number field L, not a completed/degrees-renormalized
extension and not an independently chosen valuation ring. -/
abbrev Trait (v : FinitePlace L) := Localization.AtPrime v.maximalIdeal.asIdeal

@[expose] def intoL (v : FinitePlace L) : Algebra (Trait v) L :=
  IsLocalization.localizationAlgebraOfSubmonoidLe (Trait v) L
    v.maximalIdeal.asIdeal.primeCompl ((𝓞 L)⁰)
    v.maximalIdeal.asIdeal.primeCompl_le_nonZeroDivisors

attribute [local instance] intoL

instance tower (v : FinitePlace L) : IsScalarTower (𝓞 L) (Trait v) L :=
  IsLocalization.localization_isScalarTower_of_submonoid_le (Trait v) L
    v.maximalIdeal.asIdeal.primeCompl ((𝓞 L)⁰)
    v.maximalIdeal.asIdeal.primeCompl_le_nonZeroDivisors

instance fraction (v : FinitePlace L) : IsFractionRing (Trait v) L :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    v.maximalIdeal.asIdeal.primeCompl (Trait v) L

instance discrete (v : FinitePlace L) : IsDiscreteValuationRing (Trait v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L)
    v.maximalIdeal.ne_bot (Trait v)

instance polynomialNormal (v : FinitePlace L) : IsIntegrallyClosed (Polynomial (Trait v)) := by
  infer_instance

/-- Check the actual normalized absolute value: a denominator outside
the indicated prime has value exactly one, with no completion factor. -/
theorem integral_norm (v : FinitePlace L) (z : Trait v) :
    v (algebraMap (Trait v) L z) ≤ 1 := by
  obtain ⟨a,s,rfl⟩ := IsLocalization.exists_mk'_eq v.maximalIdeal.asIdeal.primeCompl z
  have hden : v (algebraMap (𝓞 L) L (s : 𝓞 L)) = 1 :=
    (v.norm_embedding_eq _).symm.trans
      ((NumberField.FinitePlace.norm_eq_one_iff_notMem L v.maximalIdeal (s : 𝓞 L)).2 s.property)
  have hnum : v (algebraMap (𝓞 L) L a) ≤ 1 :=
    le_trans (le_of_eq (v.norm_embedding_eq _).symm)
      (NumberField.FinitePlace.norm_le_one L v.maximalIdeal a)
  have hprod := congrArg (algebraMap (Trait v) L) (IsLocalization.mk'_spec (Trait v) a s)
  have ht (t : 𝓞 L) : algebraMap (Trait v) L (algebraMap (𝓞 L) (Trait v) t) =
      algebraMap (𝓞 L) L t := (IsScalarTower.algebraMap_apply _ _ _ t).symm
  rw [map_mul,ht,ht] at hprod
  have hh := congrArg (fun t : L => v t) hprod
  rw [map_mul,hden,mul_one] at hh
  exact hh.le.trans hnum

end SelectedActualNumberFieldPlaceTrait318

#print axioms SelectedActualNumberFieldPlaceTrait318.integral_norm
