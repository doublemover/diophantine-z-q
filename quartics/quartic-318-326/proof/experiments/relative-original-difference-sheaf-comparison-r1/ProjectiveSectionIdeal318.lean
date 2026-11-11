module
public import FiniteProjectiveEvaluationFrame318
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Ideal.Maps
public section
noncomputable section
namespace ProjectiveSectionIdeal318
open TensorProduct
open scoped TensorProduct BigOperators
universe u v w z
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]

@[expose] def evaluation (m : P) : Module.Dual R P →ₗ[R] R where
  toFun φ := φ m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual zero ideal of a section of an invertible module. Its
construction also makes sense for any module; no regularity is assumed. -/
@[expose] def ideal (m : P) : Ideal R := (evaluation R P m).range

variable [Module.Finite R P] [Module.Projective R P]

lemma ideal_zero : ideal R P (0:P)=⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨φ,rfl⟩
  change φ 0=0
  exact map_zero φ

/-- A finite-projective module is separated by its actual dual frame;
zero of the section ideal is equivalent to zero of the actual section. -/
lemma ideal_eq_bot_iff (m : P) : ideal R P m=⊥ ↔ m=0 := by
  constructor
  · intro h
    let F := FiniteProjectiveEvaluationFrame318.frame R P
    have hz (i : Fin F.size) : F.coordinate i m=0 := by
      have hi : F.coordinate i m ∈ ideal R P m := ⟨F.coordinate i,rfl⟩
      rw [h] at hi
      exact hi
    have hr := F.reconstruct m
    simpa only [hz,zero_smul,Finset.sum_const_zero] using hr.symm
  · rintro rfl
    exact ideal_zero R P

variable
  (C : Type w) [CommRing C] [Algebra R C]
  (Q : Type z) [AddCommGroup Q] [Module C Q] (e : C ⊗[R] P ≃ₗ[C] Q)

@[expose] def extendedFunctional (φ : Module.Dual R P) : Module.Dual C Q :=
  (((Algebra.linearMap R C).comp φ).liftBaseChange C).comp e.symm.toLinearMap

lemma functional_unit (φ : Module.Dual R P) (m : P) :
    extendedFunctional R P C Q e φ (e ((1:C) ⊗ₜ[R] m))=algebraMap R C (φ m) := by
  change ((Algebra.linearMap R C).comp φ).liftBaseChange C
    (e.symm (e ((1:C) ⊗ₜ[R] m)))=_
  rw [LinearEquiv.symm_apply_apply,LinearMap.liftBaseChange_tmul,one_smul]
  rfl

/-- The actual section zero ideal commutes with EVERY coefficient change
when the ORIGINAL module is finite projective. It uses a produced finite
retract, not surjectivity of dual base change as an assumed premise. -/
lemma base_change (m : P) :
    ideal C Q (e ((1:C) ⊗ₜ[R] m))=Ideal.map (algebraMap R C) (ideal R P m) := by
  classical
  apply le_antisymm
  · rintro x ⟨φ,rfl⟩
    let F := FiniteProjectiveEvaluationFrame318.frame R P
    have hr : e ((1:C) ⊗ₜ[R] m)=
        ∑ i, algebraMap R C (F.coordinate i m) • e ((1:C) ⊗ₜ[R] F.vector i) := by
      calc
        e ((1:C) ⊗ₜ[R] m) = e ((1:C) ⊗ₜ[R] (∑ i, F.coordinate i m • F.vector i)) :=
          congrArg (fun y => e ((1:C) ⊗ₜ[R] y)) (F.reconstruct m).symm
        _ = _ := by
          rw [tmul_sum,map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [tmul_smul]
          simp only [Algebra.smul_def,mul_one,← smul_tmul',map_smul]
    change φ (e ((1:C) ⊗ₜ[R] m)) ∈ _
    rw [hr,map_sum]
    apply Ideal.sum_mem
    intro i _
    rw [map_smul,smul_eq_mul]
    apply Ideal.mul_mem_right
    exact Ideal.mem_map_of_mem (algebraMap R C) ⟨F.coordinate i,rfl⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro x ⟨φ,rfl⟩
    exact ⟨extendedFunctional R P C Q e φ,functional_unit R P C Q e φ m⟩

end ProjectiveSectionIdeal318
