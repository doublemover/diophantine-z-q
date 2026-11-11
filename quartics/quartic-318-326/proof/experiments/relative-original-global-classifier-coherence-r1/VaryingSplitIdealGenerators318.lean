module
public import VaryingWordGlobalClosedQuotient318
public section
noncomputable section
namespace VaryingSplitIdealGenerators318
open CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S]
variable {M : Type u} [AddCommGroup M] [Module S M]
  (ρ : (S ⊗[R] A) →ₐ[S] Module.End S M) (v : M)
  (s : M →ₗ[S] (S ⊗[R] A))
  (hs : (evaluation ρ v).comp s=LinearMap.id)
@[expose] def defect : (S ⊗[R] A) →ₗ[S] (S ⊗[R] A) := LinearMap.id-s.comp (evaluation ρ v)
@[expose] def relation (a : A) : S ⊗[R] A := defect R A S ρ v s ((1 : S) ⊗ₜ[R] a)
@[expose] def relations : Ideal (S ⊗[R] A) := Ideal.span (Set.range (relation R A S ρ v s))
include hs
lemma evaluation_defect (z : S ⊗[R] A) : evaluation ρ v (defect R A S ρ v s z)=0 := by
  change evaluation ρ v (z-s (evaluation ρ v z))=0
  rw [map_sub,show evaluation ρ v (s (evaluation ρ v z))=evaluation ρ v z from
    congrArg (fun f : M →ₗ[S] M => f (evaluation ρ v z)) hs,sub_self]
omit hs in
lemma defect_mem (z : S ⊗[R] A) : defect R A S ρ v s z ∈ relations R A S ρ v s := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | tmul c a =>
    have hc : c ⊗ₜ[R] a=c • ((1 : S) ⊗ₜ[R] a) := by
      simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rw [hc,map_smul]
    exact ((relations R A S ρ v s).restrictScalars S).smul_mem c
      (Ideal.subset_span (Set.mem_range_self a))

/-- Any genuine evaluation section generates the FULL original source
ideal, without requiring a global word basis or a reduced coefficient ring. -/
lemma ideal_eq_relations : ideal ρ v=relations R A S ρ v s := by
  apply le_antisymm
  · intro z hz
    have he : evaluation ρ v z=0 := hz
    have hd : defect R A S ρ v s z=z := by
      change z-s (evaluation ρ v z)=z
      rw [he,map_zero,sub_zero]
    exact hd ▸ defect_mem R A S ρ v s z
  · apply Ideal.span_le.mpr
    rintro z ⟨a,rfl⟩
    exact evaluation_defect R A S ρ v s hs ((1 : S) ⊗ₜ[R] a)
end VaryingSplitIdealGenerators318
