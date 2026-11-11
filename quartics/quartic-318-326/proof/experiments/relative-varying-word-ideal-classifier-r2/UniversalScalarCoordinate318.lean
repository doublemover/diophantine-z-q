module
public import SymmetricScalarRegular318
public import ProjectiveSectionParameter318
public section
noncomputable section
namespace UniversalScalarCoordinate318
open scoped BigOperators TensorProduct
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
  (B : Type w) [CommRing B] [Algebra R B]
  (ell : P →ₗ[R] B)
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "D" => Module.Dual R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P

/-- Evaluate the SAME universal tensor along an actual B-valued original
section-coordinate map. The result lives in the actual scalar-extended
parameter ring, not in a newly named unrelated symmetric algebra. -/
@[expose] def evaluate : A ⊗[R] P →ₗ[R] B ⊗[R] A :=
  (TensorProduct.comm R A B).toLinearMap.comp (TensorProduct.map LinearMap.id ell)

lemma evaluate_tmul (a : A) (p : P) : evaluate R P B ell (a ⊗ₜ[R] p)=ell p ⊗ₜ[R] a := rfl

lemma universal_sum : ProjectiveSectionParameter318.universal R P =
    ∑ i, SymmetricAlgebra.ι R D (F.coordinate i) ⊗ₜ[R] F.vector i := by
  apply (FiniteProjectiveTensorDual318.equivalence R P A F).injective
  ext φ
  change FiniteProjectiveTensorDual318.pairing R P A
    (ProjectiveSectionParameter318.universal R P) φ =
      FiniteProjectiveTensorDual318.pairing R P A
        (∑ i, SymmetricAlgebra.ι R D (F.coordinate i) ⊗ₜ[R] F.vector i) φ
  rw [ProjectiveSectionParameter318.universal_coordinate,map_sum,LinearMap.sum_apply]
  simp only [FiniteProjectiveTensorDual318.pairing_tmul]
  have h := congrArg (SymmetricAlgebra.ι R D) (F.dual_reconstruct φ)
  rw [map_sum] at h
  simp only [map_smul,Algebra.smul_def] at h
  simpa only [mul_comm] using h.symm

@[expose] def primitive : B ⊗[R] D := ∑ i, ell (F.vector i) ⊗ₜ[R] F.coordinate i
@[expose] def coefficient : B ⊗[R] A :=
  evaluate R P B ell (ProjectiveSectionParameter318.universal R P)

lemma coefficient_sum : coefficient R P B ell =
    ∑ i, ell (F.vector i) ⊗ₜ[R] SymmetricAlgebra.ι R D (F.coordinate i) := by
  rw [coefficient,universal_sum,map_sum]
  rfl

/-- Exact symmetric scalar-change formula for the evaluated ACTUAL
universal tensor, including all original finite dual-frame coefficients. -/
lemma scalar_comparison : SymmetricScalarChange318.equivalence R B D (coefficient R P B ell) =
    SymmetricAlgebra.ι B (B ⊗[R] D) (primitive R P B ell) := by
  rw [coefficient_sum,map_sum,primitive,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change SymmetricScalarChange318.forward R B D _ = _
  rw [SymmetricScalarChange318.forward_tmul_generator,← map_smul]
  congr 1
  rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]

@[expose] def evaluationAt (s : B ⊗[R] P) : (B ⊗[R] D) →ₗ[B] B :=
  (FiniteProjectiveTensorDual318.pairing R P B s).liftBaseChange B

lemma evaluation_primitive (s : B ⊗[R] P) :
    evaluationAt R P B s (primitive R P B ell) = ell.liftBaseChange B s := by
  have hs (z : B ⊗[R] P) : evaluationAt R P B z (primitive R P B ell) =
      ∑ i, ell (F.vector i) * FiniteProjectiveTensorDual318.pairing R P B z (F.coordinate i) := by
    rw [primitive,map_sum]
    rfl
  rw [hs]
  induction s using TensorProduct.inductionOn with
  | tmul b p =>
      simp only [FiniteProjectiveTensorDual318.pairing_tmul,LinearMap.liftBaseChange_tmul,smul_eq_mul]
      have h := congrArg ell (F.reconstruct p)
      rw [map_sum] at h
      simp only [map_smul,Algebra.smul_def] at h
      calc
        _ = b * ∑ i, algebraMap R B (F.coordinate i p) * ell (F.vector i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [h]
  | add x y hx hy =>
      simp only [map_add,LinearMap.add_apply,mul_add,Finset.sum_add_distrib,hx,hy]

/-- A produced value-one vector in the scalar-extended actual global
section module makes the evaluated universal coordinate regular over the
original scalar-extended parameter ring. No flatness of R to B is needed. -/
theorem regular (s : B ⊗[R] P) (hs : ell.liftBaseChange B s=1)
    (a : B ⊗[R] A) (ha : a * coefficient R P B ell=0) : a=0 := by
  have hv : evaluationAt R P B s (primitive R P B ell)=1 :=
    (evaluation_primitive R P B ell s).trans hs
  have hc : coefficient R P B ell = (SymmetricScalarChange318.equivalence R B D).symm
      (SymmetricAlgebra.ι B (B ⊗[R] D) (primitive R P B ell)) := by
    apply (SymmetricScalarChange318.equivalence R B D).injective
    rw [scalar_comparison,AlgEquiv.apply_symm_apply]
  rw [hc] at ha
  exact SymmetricScalarRegular318.regular R B D (primitive R P B ell)
    (evaluationAt R P B s) hv a ha
end UniversalScalarCoordinate318
