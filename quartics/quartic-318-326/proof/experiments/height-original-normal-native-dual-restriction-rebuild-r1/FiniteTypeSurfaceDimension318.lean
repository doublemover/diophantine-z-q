module
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public section
noncomputable section
namespace FiniteTypeSurfaceDimension318
open scoped Cardinal
/-- Integral maps preserve strict inclusion of prime ideals under
contraction. This yields the needed genuine Krull upper bound directly,
without identifying transcendence degree and dimension by fiat. -/
theorem integral_dimension_le {R S:Type*}[CommRing R][CommRing S]
    (f:R→+*S)(hf:f.IsIntegral):ringKrullDim S≤ringKrullDim R:=by
  letI:Algebra R S:=f.toAlgebra
  letI:Algebra.IsIntegral R S:=⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro I J hIJ
  letI:I.asIdeal.IsPrime:=I.isPrime
  change I.asIdeal.under R<J.asIdeal.under R
  exact Ideal.IsIntegral.under_lt_under (show I.asIdeal<J.asIdeal from hIJ)
variable (A:Type)[CommRing A][Nontrivial A][Algebra ℂ A][Algebra.FiniteType ℂ A]
/-- Actual Noether normalization is PRODUCED for the same scalar algebra.
Its number of independent polynomial variables is at most two, by the
already-proved bound for ALL algebraically independent subsets. -/
theorem normalization_two(h:Algebra.trdeg ℂ A≤2):
    ∃s:ℕ,s≤2∧∃g:MvPolynomial (Fin s) ℂ→ₐ[ℂ]A,Function.Injective g∧g.IsIntegral:=by
  obtain ⟨s,g,hg,hint⟩:=exists_integral_inj_algHom_of_fg ℂ A
  have hi:= (MvPolynomial.algebraicIndependent_X (Fin s) ℂ).map' (f:=g) hg
  have hc:(s:Cardinal)≤2:=by
    simpa using hi.cardinalMk_le_trdeg.trans h
  have hs:s≤2:=by exact_mod_cast hc
  exact ⟨s,hs,g,hg,hint⟩
/-- Genuine Krull dimension bound, through an actual integral
normalization map and its strict prime-contraction map. -/
theorem krull_dimension_le_two(h:Algebra.trdeg ℂ A≤2):ringKrullDim A≤2:=by
  obtain ⟨s,hs,g,hg,hint⟩:=normalization_two A h
  calc
    ringKrullDim A≤ringKrullDim (MvPolynomial (Fin s) ℂ):=
      integral_dimension_le g.toRingHom hint
    _=(s:WithBot ℕ∞):=by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field,Nat.card_fin,zero_add]
    _≤2:=by exact_mod_cast hs
end FiniteTypeSurfaceDimension318
