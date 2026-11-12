module
public import Mathlib.LinearAlgebra.Quotient.Basic
public section
noncomputable section
namespace TwoChartJetDifferential318
universe u v w z
variable {R : Type u} [CommRing R]
  {A : Type v} [AddCommGroup A] [Module R A]
  {B : Type w} [AddCommGroup B] [Module R B]
  {M : Type z} [AddCommGroup M] [Module R M]
  (f : A →ₗ[R] M) (g : B →ₗ[R] M) (t : B →ₗ[R] B) (v : M ≃ₗ[R] M)
  (h : ∀ b, v (g (t b)) = g b)

@[expose] def difference : (A × B) →ₗ[R] M :=
  f.comp (LinearMap.fst R A B) - g.comp (LinearMap.snd R A B)
@[expose] def positiveDifference : (A × B) →ₗ[R] M :=
  difference f (v.toLinearMap.comp g)

/-- The finite candidate differential sends an ACTUAL positive-twist
section pair to the jet of its infinity coordinate. -/
@[expose] def jet : LinearMap.ker (positiveDifference f g v) →ₗ[R] B ⧸ t.range :=
  t.range.mkQ.comp ((LinearMap.snd R A B).comp (LinearMap.ker (positiveDifference f g v)).subtype)

@[expose] def inclusion : LinearMap.ker (difference f g) →ₗ[R]
    LinearMap.ker (positiveDifference f g v) where
  toFun x := ⟨(x.val.1,t x.val.2),by
    change f x.val.1-v (g (t x.val.2))=0
    rw [h]
    exact x.property⟩
  map_add' x y := by apply Subtype.ext; exact Prod.ext rfl (map_add t _ _)
  map_smul' r x := by apply Subtype.ext; exact Prod.ext rfl (map_smul t _ _)

lemma jet_inclusion (x : LinearMap.ker (difference f g)) :
    jet f g t v (inclusion f g t v h x)=0 := by
  change t.range.mkQ (t x.val.2)=0
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact ⟨x.val.2,rfl⟩

@[expose] def kernelMap : LinearMap.ker (difference f g) →ₗ[R]
    LinearMap.ker (jet f g t v) :=
  (inclusion f g t v h).codRestrict _ (jet_inclusion f g t v h)

include h in
lemma kernelMap_surjective : Function.Surjective (kernelMap f g t v h) := by
  intro x
  have hx : x.val.val.2 ∈ t.range := by
    have hz := x.property
    change t.range.mkQ x.val.val.2=0 at hz
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨b,hb⟩ := hx
  have hc : f x.val.val.1-g b=0 := by
    have hy := x.val.property
    change f x.val.val.1-v (g x.val.val.2)=0 at hy
    rw [← hb,h] at hy
    exact hy
  refine ⟨⟨(x.val.val.1,b),hc⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext rfl hb

include h in
lemma kernelMap_injective (ht : Function.Injective t) :
    Function.Injective (kernelMap f g t v h) := by
  intro x y hxy
  have hp := congrArg (fun z : LinearMap.ker (jet f g t v) => z.val.val) hxy
  apply Subtype.ext
  exact Prod.ext (congrArg Prod.fst hp) (ht (congrArg Prod.snd hp))

/-- The degree-zero comparison is the ACTUAL inclusion (a,b)↦(a,u^n b),
not a dimension or presentation replacement. -/
@[expose] def kernelEquivalence (ht : Function.Injective t) :
    LinearMap.ker (difference f g) ≃ₗ[R] LinearMap.ker (jet f g t v) :=
  LinearEquiv.ofBijective (kernelMap f g t v h)
    ⟨kernelMap_injective f g t v h ht,kernelMap_surjective f g t v h⟩
end TwoChartJetDifferential318
