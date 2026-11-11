module
public import CyclicQuotientEvaluation318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
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
  simpa only [quotientEquiv,LinearEquiv.trans_apply,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk,
    Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivOfSurjective_apply_mk, evaluation]

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
