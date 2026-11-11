module
public import VaryingSourceWordQuotient318
public section
noncomputable section
namespace VaryingSourceGeneratorSpan318
open VaryingSourceActionClassifier318 VaryingSourceTensorAction318
open CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Action R A ι S)
@[expose] def generator (x : A) : ι → S := a.map x *ᵥ a.marked

/-- Cyclicity of the full original coefficient tensor source implies
spanning by the literal original-element columns, not merely by arbitrary
tensor elements. This is the needed input for extracting word charts. -/
lemma span_eq_top
    (h : Function.Surjective (evaluation (linearAction R A ι S a) a.marked)) :
    Submodule.span S (Set.range (generator R A ι S a))=⊤ := by
  apply top_unique
  intro y _
  obtain ⟨z,rfl⟩ := h y
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact (Submodule.span S (Set.range (generator R A ι S a))).zero_mem
  | tmul s x =>
    change linearAction R A ι S a (s ⊗ₜ[R] x) a.marked ∈ _
    rw [linearAction_tmul,Matrix.smul_mulVec]
    exact Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_range_self x))
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
end VaryingSourceGeneratorSpan318
