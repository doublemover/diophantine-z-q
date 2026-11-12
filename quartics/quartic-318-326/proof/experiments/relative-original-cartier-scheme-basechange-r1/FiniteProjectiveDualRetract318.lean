module
public import FiniteProjectiveEvaluationFrame318
public section
noncomputable section
namespace FiniteProjectiveDualRetract318
universe u
open scoped BigOperators
variable (S P : Type u) [CommRing S] [AddCommGroup P] [Module S P]
  (F : FiniteProjectiveEvaluationFrame318.Frame S P)

@[expose] def out : Module.Dual S P →ₗ[S] (Fin F.size → S) where
  toFun φ i := φ (F.vector i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[expose] def back : (Fin F.size → S) →ₗ[S] Module.Dual S P where
  toFun a := ∑ i, a i • F.coordinate i
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma total : (back S P F).comp (out S P F) = LinearMap.id := by
  ext φ x
  exact congrArg (fun ψ : Module.Dual S P => ψ x) (F.dual_reconstruct φ)

lemma properties : Module.Finite S (Module.Dual S P) ∧
    Module.Projective S (Module.Dual S P) := by
  have hs : Function.Surjective (back S P F) := fun φ =>
    ⟨out S P F φ, LinearMap.congr_fun (total S P F) φ⟩
  exact ⟨Module.Finite.of_surjective _ hs,
    Module.Projective.of_split (out S P F) (back S P F) (total S P F)⟩
end FiniteProjectiveDualRetract318
