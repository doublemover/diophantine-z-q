module
public import FinitePolynomialRetractPresentation318
public import FiniteProjectiveEvaluationFrame318
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public section
noncomputable section
namespace ProjectiveSymmetricPresentation318
open scoped BigOperators
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
  (F : FiniteProjectiveEvaluationFrame318.Frame R M)
local notation "A" => SymmetricAlgebra R M
local notation "B" => MvPolynomial (Fin F.size) R

@[expose] def out : A →ₐ[R] B := SymmetricAlgebra.lift
  { toFun := fun m => ∑ i,F.coordinate i m • MvPolynomial.X i
    map_add' := by intro a b; simp only [map_add,add_smul,Finset.sum_add_distrib]
    map_smul' := by intro r m; simp only [map_smul,smul_eq_mul,mul_smul,Finset.smul_sum] }
@[expose] def back : B →ₐ[R] A := MvPolynomial.aeval (fun i => SymmetricAlgebra.ι R M (F.vector i))

lemma total : (back R M F).comp (out R M F)=AlgHom.id R A := by
  apply SymmetricAlgebra.algHom_ext
  ext m
  change back R M F (SymmetricAlgebra.lift _ (SymmetricAlgebra.ι R M m))=SymmetricAlgebra.ι R M m
  rw [SymmetricAlgebra.lift_ι_apply]
  change back R M F (∑ i,F.coordinate i m • MvPolynomial.X i)=_
  simp only [map_sum,map_smul,back,MvPolynomial.aeval_X]
  simpa only [map_sum,map_smul] using congrArg (SymmetricAlgebra.ι R M) (F.reconstruct m)

/-- The symmetric algebra of the actual finite-projective module has a
finite presentation obtained from its ORIGINAL finite dual-frame retract. -/
lemma finitePresentation : Algebra.FinitePresentation R A :=
  FinitePolynomialRetractPresentation318.finitePresentation R A F.size
    (back R M F) (out R M F) (total R M F)
end ProjectiveSymmetricPresentation318
