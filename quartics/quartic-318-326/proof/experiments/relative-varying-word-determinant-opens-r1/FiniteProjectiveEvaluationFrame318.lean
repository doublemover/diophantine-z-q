module
public import FiniteProjectiveDualFrame318
public import Mathlib.LinearAlgebra.Dual.Lemmas
public section
noncomputable section
namespace FiniteProjectiveEvaluationFrame318
open scoped BigOperators
universe u v
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]

/-- A finite dual frame records the actual projective retraction, without
claiming that a projective module over an arbitrary ring is free. -/
structure Frame where
  size : ℕ
  vector : Fin size → P
  coordinate : Fin size → Module.Dual R P
  reconstruct : ∀ x : P, ∑ i, coordinate i x • vector i=x

variable [Module.Finite R P] [Module.Projective R P]

@[expose] def frame : Frame R P := by
  let F := FiniteProjectiveDualFrame318.frame R P
  refine ⟨F.n,fun i => F.back i 1,F.out,?_⟩
  intro x
  have h := LinearMap.congr_fun F.total x
  have hb (i : Fin F.n) (r : R) : F.back i r=r • F.back i 1 := by
    simpa only [smul_eq_mul,mul_one] using (F.back i).map_smul r (1:R)
  simpa only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.id_apply,hb] using h

end FiniteProjectiveEvaluationFrame318
namespace FiniteProjectiveEvaluationFrame318.Frame
open scoped BigOperators
universe u v
variable {R : Type u} [CommRing R] {P : Type v} [AddCommGroup P] [Module R P]
  (F : FiniteProjectiveEvaluationFrame318.Frame R P)

/-- The same actual frame reconstructs EVERY dual functional. -/
lemma dual_reconstruct (φ : Module.Dual R P) : ∑ i, φ (F.vector i) • F.coordinate i=φ := by
  ext x
  have h := congrArg φ (F.reconstruct x)
  rw [map_sum] at h
  simp only [map_smul] at h
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,mul_comm] using h
end FiniteProjectiveEvaluationFrame318.Frame
