module
public import SelectedPrincipalPrimeNormalIntersection318
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Spectrum.Maximal.Localization
public section
noncomputable section

open SelectedPrincipalPrimeNormalIntersection318

namespace SelectedDedekindFractionWitness318

variable {B F : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
variable [Field F] [Algebra B F] [IsFractionRing B F]

attribute [local instance] SelectedPrincipalPrimeNormalIntersection318.localAlgebra

private theorem clear_fraction (q : PrimeSpectrum B) (z : F)
    (h : IsLocalization.IsInteger (localRing q) z) :
    ∃ a s : B, s∉q.asIdeal ∧ z * algebraMap B F s = algebraMap B F a := by
  obtain ⟨r,hr⟩ := h
  obtain ⟨a,s,hs⟩ := IsLocalization.exists_mk'_eq q.asIdeal.primeCompl r
  have hl : r * algebraMap B (localRing q) (s:B) = algebraMap B (localRing q) a := by
    rw [←hs]
    exact IsLocalization.mk'_spec (localRing q) a s
  have hf := congrArg (algebraMap (localRing q) F) hl
  refine ⟨a,s,s.2,?_⟩
  simpa only [map_mul,hr,←IsScalarTower.algebraMap_apply B (localRing q) F] using hf

/-- A nonintegral element of a Dedekind domain's own fraction field has
a multiple by an element of the domain that is integral and nonzero
at one maximal ideal. The denominator ideal finds the actual prime;
the inverse is taken only in the same fraction field. -/
theorem exists_integral_multiple_residue (z : F)
    (hz : ¬IsLocalization.IsInteger B z) :
    ∃ P : MaximalSpectrum B, ∃ a s : B, s∉P.asIdeal ∧
      z*algebraMap B F a=algebraMap B F s := by
  let I : Ideal B := (1 : Submodule B F).comap (LinearMap.toSpanSingleton B F z)
  have hI : I≠⊤ := by
    intro he
    have h : (1:B)∈I := he.symm ▸ (Submodule.mem_top : (1:B)∈(⊤ : Ideal B))
    change (1:B) • z ∈ (1 : Submodule B F) at h
    apply hz
    rw [one_smul] at h
    exact Submodule.mem_one.mp h
  obtain ⟨P,hP,hle⟩ := Ideal.exists_le_maximal I hI
  let q : PrimeSpectrum B := ⟨P,hP.isPrime⟩
  letI : ValuationRing (localRing q) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (localRing q)).out 2 1).mp inferInstance
  have hBad : ¬ IsLocalization.IsInteger (localRing q) z := by
    intro h
    obtain ⟨a,s,hs,he⟩ := clear_fraction q z h
    have hi : s∈I := by
      change s • z ∈ (1 : Submodule B F)
      apply Submodule.mem_one.mpr
      refine ⟨a,?_⟩
      rw [Algebra.smul_def,mul_comm]
      exact he.symm
    exact hs (hle hi)
  have hinv : IsLocalization.IsInteger (localRing q) z⁻¹ :=
    (ValuationRing.isInteger_or_isInteger (localRing q) z).resolve_left hBad
  obtain ⟨a,s,hs,he⟩ := clear_fraction q z⁻¹ hinv
  refine ⟨⟨P,hP⟩,a,s,hs,?_⟩
  have hz0 : z≠0 := fun h => hz ⟨0,(map_zero _).trans h.symm⟩
  rw [←he,←mul_assoc,mul_inv_cancel₀ hz0,one_mul]

end SelectedDedekindFractionWitness318

#print axioms SelectedDedekindFractionWitness318.exists_integral_multiple_residue
