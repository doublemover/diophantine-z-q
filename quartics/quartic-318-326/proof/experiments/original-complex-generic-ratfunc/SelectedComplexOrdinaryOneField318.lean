module
public import SelectedComplexConnectedNoSplit318
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic
public section
noncomputable section
open Polynomial
open scoped nonZeroDivisors
open SelectedComplexOrdinaryBase318 SelectedComplexConnectedNoSplit318

namespace SelectedComplexOrdinaryOneField318

private theorem denominator_ne : denominator ≠ 0 := by
  unfold denominator
  exact mul_ne_zero Polynomial.X_ne_zero
    (by simpa using Polynomial.X_sub_C_ne_zero (1728 : ℂ))

theorem coefficient_domain : IsDomain Base :=
  IsLocalization.Away.isDomain _ denominator_ne

theorem coefficient_normal : IsIntegrallyClosed Base := by
  letI : IsDomain Base := coefficient_domain
  apply isIntegrallyClosed_of_isLocalization Base (Submonoid.powers denominator)
  rintro _ ⟨i,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero i denominator_ne)

abbrev Generic := FractionRing Base
abbrev genericPolynomial (p : Base[X]) : Generic[X] := p.map (algebraMap Base Generic)

theorem coefficient_irreducible (p : Base[X]) (hp : p.Monic) (hpdeg : 0 < p.natDegree)
    (hc : IsPreconnected (roots p))
    (simple : ∀ z ∈ roots p, p.derivative.eval₂ (evaluation z.1) z.2 ≠ 0) :
    Irreducible p := by
  letI : IsDomain Base := coefficient_domain
  apply hp.irreducible_iff_natDegree.mpr
  refine ⟨?_,?_⟩
  · intro he
    rw [he,natDegree_one] at hpdeg
    exact (Nat.lt_irrefl 0) hpdeg
  · intro a b ha hb hprod
    by_cases ha0 : a.natDegree = 0
    · exact Or.inl ha0
    · right
      by_contra hb0
      exact no_positive_monic_split p a b ha hb (Nat.pos_of_ne_zero ha0)
        (Nat.pos_of_ne_zero hb0) hc simple hprod.symm

/-- The whole connected simple-root chart gives one generic field,
not a selected simple factor of a preexisting scalar extension. -/
theorem generic_irreducible (p : Base[X]) (hp : p.Monic) (hpdeg : 0 < p.natDegree)
    (hc : IsPreconnected (roots p))
    (simple : ∀ z ∈ roots p, p.derivative.eval₂ (evaluation z.1) z.2 ≠ 0) :
    Irreducible (genericPolynomial p) := by
  letI : IsDomain Base := coefficient_domain
  letI : IsIntegrallyClosed Base := coefficient_normal
  exact (hp.irreducible_iff_irreducible_map_fraction_map (K := Generic)).mp
    (coefficient_irreducible p hp hpdeg hc simple)

theorem generic_isField (p : Base[X]) (hp : p.Monic) (hpdeg : 0 < p.natDegree)
    (hc : IsPreconnected (roots p))
    (simple : ∀ z ∈ roots p, p.derivative.eval₂ (evaluation z.1) z.2 ≠ 0) :
    IsField (AdjoinRoot (genericPolynomial p)) := by
  letI : IsDomain Base := coefficient_domain
  exact AdjoinRoot.isField_iff_irreducible.mpr (generic_irreducible p hp hpdeg hc simple)

end SelectedComplexOrdinaryOneField318

#print axioms SelectedComplexOrdinaryOneField318.coefficient_irreducible
#print axioms SelectedComplexOrdinaryOneField318.generic_isField
