module
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.Data.Complex.Basic
public section
noncomputable section
namespace SimpleLocalComplexDimension318
variable {R M : Type*} [CommRing R] [IsLocalRing R] [Algebra ℂ R]
  [AddCommGroup M] [Module R M] [Module ℂ M] [IsScalarTower ℂ R M]
/-- A length-one actual local module is a one-dimensional complex
vector space once the SAME structural map identifies its residue field
with C. The residue-field condition is an explicit separate input. -/
theorem exists_linearEquiv (h : Module.length R M = 1)
    (hr : Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField R))) :
    Nonempty (M ≃ₗ[ℂ] ℂ) := by
  haveI : IsSimpleModule R M := Module.length_eq_one_iff.mp h
  obtain ⟨I,hI,⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := R) (M := M)).mp inferInstance
  have hi : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
  subst I
  let er : ℂ ≃ₐ[ℂ] IsLocalRing.ResidueField R :=
    AlgEquiv.ofBijective (Algebra.ofId ℂ (IsLocalRing.ResidueField R)) hr
  exact ⟨(e.restrictScalars ℂ).trans er.symm.toLinearEquiv⟩
theorem finrank_one (h : Module.length R M = 1)
    (hr : Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField R))) :
    Module.finrank ℂ M = 1 := by
  obtain ⟨e⟩ := exists_linearEquiv h hr
  rw [e.finrank_eq]
  exact Module.finrank_self ℂ
theorem finite (h : Module.length R M = 1)
    (hr : Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField R))) :
    Module.Finite ℂ M := by
  obtain ⟨e⟩ := exists_linearEquiv h hr
  exact Module.Finite.equiv e.symm
end SimpleLocalComplexDimension318
