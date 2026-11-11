module
public import DualAffinePointedTriviality318
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace DualNumberScalarExtension318
open scoped TensorProduct
open TrivSqZeroExt
universe u v
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
abbrev Tensor := S ⊗[R] DualNumber R
/-- The original coefficient map, preserving the actual epsilon. -/
@[expose] def baseMap : DualNumber R →ₐ[R] DualNumber S :=
  DualNumber.lift ⟨(Algebra.ofId R (DualNumber S), DualNumber.eps),
    DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩
@[simp] lemma baseMap_eps : baseMap R S DualNumber.eps = DualNumber.eps :=
  DualNumber.lift_apply_eps _
@[expose] def forward : Tensor R S →ₐ[R] DualNumber S :=
  Algebra.TensorProduct.lift (inlAlgHom R S S) (baseMap R S) (fun _ _ => Commute.all _ _)
@[simp] lemma forward_left (s : S) : forward R S (s ⊗ₜ[R] 1) = inl s := by
  simp [forward]
@[simp] lemma forward_right (d : DualNumber R) : forward R S (1 ⊗ₜ[R] d) = baseMap R S d := by
  simp [forward]
@[expose] def backward : DualNumber S →ₐ[R] Tensor R S :=
  DualNumber.lift ⟨(Algebra.TensorProduct.includeLeft,
    (Algebra.TensorProduct.includeRight : DualNumber R →ₐ[R] Tensor R S) DualNumber.eps),
    by rw [← map_mul, DualNumber.eps_mul_eps, map_zero], fun _ => Commute.all _ _⟩
@[simp] lemma backward_inl (s : S) : backward R S (inl s) = s ⊗ₜ[R] 1 := by
  rw [backward,DualNumber.lift_apply_inl]
@[simp] lemma backward_eps : backward R S (DualNumber.eps : DualNumber S) = 1 ⊗ₜ[R] (DualNumber.eps : DualNumber R) := by
  rw [backward,DualNumber.lift_apply_eps]
lemma forward_backward : (forward R S).comp (backward R S) = AlgHom.id R (DualNumber S) := by
  apply TrivSqZeroExt.algHom_ext'
  · apply AlgHom.ext
    intro s
    change forward R S (backward R S (inl s)) = inl s
    simp only [backward_inl, forward_left]
  · apply LinearMap.ext
    intro s
    change forward R S (backward R S (inr s)) = inr s
    rw [DualNumber.inr_eq_smul_eps, ← TrivSqZeroExt.inl_mul_eq_smul,
      map_mul, backward_inl, backward_eps, map_mul, forward_left, forward_right, baseMap_eps]
    exact (TrivSqZeroExt.inl_mul_eq_smul _ _).trans (DualNumber.inr_eq_smul_eps s).symm
lemma backward_forward : (backward R S).comp (forward R S) = AlgHom.id R (Tensor R S) := by
  apply Algebra.TensorProduct.ext
  · ext s
    change backward R S (forward R S (s ⊗ₜ[R] 1)) = s ⊗ₜ[R] 1
    simp only [forward_left, backward_inl]
  · apply DualNumber.algHom_ext
    change backward R S (forward R S (1 ⊗ₜ[R] DualNumber.eps)) = 1 ⊗ₜ[R] DualNumber.eps
    simp only [forward_right, baseMap_eps, backward_eps]
/-- The actual scalar-extension ring, with both original generators fixed. -/
@[expose] def equivalence : Tensor R S ≃ₐ[R] DualNumber S :=
  AlgEquiv.ofAlgHom (forward R S) (backward R S) (forward_backward R S) (backward_forward R S)
@[simp] lemma equivalence_left (s : S) : equivalence R S (s ⊗ₜ[R] 1) = inl s := forward_left R S s
@[simp] lemma equivalence_epsilon : equivalence R S (1 ⊗ₜ[R] DualNumber.eps) = DualNumber.eps := by
  exact (forward_right R S _).trans (baseMap_eps R S)
/-- Literal augmentation of the original tensor algebra. -/
@[expose] def reduction : Tensor R S →+* S :=
  (DualNumberScheme318.reductionRing S).comp (equivalence R S).toRingHom
@[expose] def sectionMap : S →+* Tensor R S := Algebra.TensorProduct.includeLeftRingHom
@[simp] lemma reduction_section (s : S) : reduction R S (sectionMap R S s) = s := by
  change (equivalence R S (s ⊗ₜ[R] 1)).fst = s
  rw [equivalence_left]
  rfl
@[simp] lemma reduction_right (d : DualNumber R) :
    reduction R S (1 ⊗ₜ[R] d) = algebraMap R S d.fst := by
  change (forward R S (1 ⊗ₜ[R] d)).fst = _
  rw [forward_right]
  simp [baseMap, DualNumber.lift_apply_apply, Algebra.ofId_apply,
    TrivSqZeroExt.algebraMap_eq_inl']
abbrev epsilon : Tensor R S := 1 ⊗ₜ[R] (DualNumber.eps : DualNumber R)
lemma epsilon_square : epsilon R S * epsilon R S = 0 := by
  change (Algebra.TensorProduct.includeRight : DualNumber R →ₐ[R] Tensor R S) DualNumber.eps *
    (Algebra.TensorProduct.includeRight : DualNumber R →ₐ[R] Tensor R S) DualNumber.eps = 0
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
lemma reduction_kernel : RingHom.ker (reduction R S) = Ideal.span {epsilon R S} := by
  apply le_antisymm
  · intro x hx
    have he : equivalence R S x ∈ Ideal.span {DualAffinePointedTriviality318.epsilon S} := by
      rw [← DualAffinePointedTriviality318.reduction_kernel]
      exact hx
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.1 he
    apply Ideal.mem_span_singleton'.2
    refine ⟨(equivalence R S).symm a, (equivalence R S).injective ?_⟩
    rw [map_mul, AlgEquiv.apply_symm_apply, equivalence_epsilon]
    exact ha
  · apply Ideal.span_le.2
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change (equivalence R S (epsilon R S)).fst = 0
    rw [equivalence_epsilon]
    rfl
end DualNumberScalarExtension318
