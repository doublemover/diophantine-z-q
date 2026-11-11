module
public import CyclicQuotientEvaluation318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Basis.Basic
public section
noncomputable section
namespace CyclicQuotientKernel318
open CyclicQuotientEvaluation318
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]
variable (ρ : A →ₐ[R] Module.End R M) (v : M)

/-- A cyclic action produces the genuine quotient algebra by its vector
annihilator. Its entire underlying module is the specified original M;
this is an all-ring isomorphism, not a residue-point comparison. -/
@[expose] def quotientEquiv (h : Function.Surjective (evaluation ρ v)) :
    (A ⧸ ideal ρ v) ≃ₗ[R] M :=
  ((Submodule.Quotient.restrictScalarsEquiv R (ideal ρ v)).symm.trans
    (Submodule.quotEquivOfEq _ _ (ideal_restrict ρ v))).trans
      ((evaluation ρ v).quotKerEquivOfSurjective h)

lemma quotientEquiv_mk (h : Function.Surjective (evaluation ρ v)) (a : A) :
    quotientEquiv ρ v h (Ideal.Quotient.mk (ideal ρ v) a) = ρ a v := by
  let e₀ := (Submodule.Quotient.restrictScalarsEquiv R (ideal ρ v)).symm
  let e₁ := Submodule.quotEquivOfEq _ _ (ideal_restrict ρ v)
  let e₂ := (evaluation ρ v).quotKerEquivOfSurjective h
  have h₀ : e₀ (Ideal.Quotient.mk (ideal ρ v) a)=
      (Submodule.Quotient.mk a : A ⧸ (ideal ρ v).restrictScalars R) :=
    Submodule.Quotient.restrictScalarsEquiv_symm_mk R (ideal ρ v) a
  have h₁ : e₁ (Submodule.Quotient.mk a)=
      (Submodule.Quotient.mk a : A ⧸ (evaluation ρ v).ker) :=
    Submodule.quotEquivOfEq_mk (ideal_restrict ρ v) a
  have h₂ : e₂ (Submodule.Quotient.mk a)=ρ a v :=
    LinearMap.quotKerEquivOfSurjective_apply_mk (evaluation ρ v) h a
  change e₂ (e₁ (e₀ (Ideal.Quotient.mk (ideal ρ v) a)))=ρ a v
  exact (congrArg (fun z => e₂ (e₁ z)) h₀).trans ((congrArg e₂ h₁).trans h₂)

/-- The quotient is free of the SAME rank whenever the specified cyclic
module carries this basis. No field or reducedness assumption is used. -/
@[expose] def quotientBasis {ι : Type u} (b : Basis ι R M)
    (h : Function.Surjective (evaluation ρ v)) : Basis ι R (A ⧸ ideal ρ v) :=
  b.map (quotientEquiv ρ v h).symm

lemma quotientBasis_image {ι : Type u} (b : Basis ι R M)
    (h : Function.Surjective (evaluation ρ v)) (i : ι) :
    quotientEquiv ρ v h (quotientBasis ρ v b h i) = b i := by
  change quotientEquiv ρ v h ((quotientEquiv ρ v h).symm (b i)) = b i
  exact (quotientEquiv ρ v h).apply_symm_apply (b i)
end CyclicQuotientKernel318
