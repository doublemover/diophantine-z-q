module
public import TwoChartJetCokernel318
public import Mathlib.Algebra.Module.Projective
public section
noncomputable section
namespace TwoChartJetChainMap318
open TwoChartJetDifferential318
universe u v w z
variable {R : Type u} [CommRing R]
  {A : Type v} [AddCommGroup A] [Module R A]
  {B : Type w} [AddCommGroup B] [Module R B]
  {M : Type z} [AddCommGroup M] [Module R M]
  (f : A →ₗ[R] M) (g : B →ₗ[R] M) (t : B →ₗ[R] B) (v : M ≃ₗ[R] M)
  (h : ∀ b, v (g (t b))=g b) (ht : Function.Injective t)
  (s : (B ⧸ t.range) →ₗ[R] B) (hs : t.range.mkQ.comp s=LinearMap.id)

@[expose] def ontoRange : B ≃ₗ[R] t.range :=
  LinearEquiv.ofBijective t.rangeRestrict ⟨fun x y hxy => ht (congrArg Subtype.val hxy),by
    rintro ⟨x,y,rfl⟩
    exact ⟨y,rfl⟩⟩

/-- Removing a chosen linear lift of the actual jet leaves an element
of the actual coordinate-power image, before any division is performed. -/
@[expose] def residual : LinearMap.ker (positiveDifference f g v) →ₗ[R] t.range :=
  (((LinearMap.snd R A B).comp (LinearMap.ker (positiveDifference f g v)).subtype) -
    s.comp (jet f g t v)).codRestrict _ (by
      intro x
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change t.range.mkQ (x.val.2-s (jet f g t v x))=0
      rw [map_sub]
      have he := LinearMap.congr_fun hs (jet f g t v x)
      change t.range.mkQ (s (jet f g t v x))=jet f g t v x at he
      rw [he]
      exact sub_self _)

@[expose] def degreeZero : LinearMap.ker (positiveDifference f g v) →ₗ[R] A × B :=
  ((LinearMap.fst R A B).comp (LinearMap.ker (positiveDifference f g v)).subtype).prod
    ((ontoRange t ht).symm.toLinearMap.comp (residual f g t v s hs))
@[expose] def degreeOne : (B ⧸ t.range) →ₗ[R] M := v.toLinearMap.comp (g.comp s)

lemma division (x : LinearMap.ker (positiveDifference f g v)) :
    t (degreeZero f g t v ht s hs x).2 = x.val.2-s (jet f g t v x) := by
  have he := (ontoRange t ht).apply_symm_apply (residual f g t v s hs x)
  exact congrArg Subtype.val he

include h in
/-- This is the ACTUAL chain-map square from the finite jet complex to
the original two-chart complex, not merely a matching cohomology count. -/
lemma square : (difference f g).comp (degreeZero f g t v ht s hs) =
    (degreeOne g t v s).comp (jet f g t v) := by
  ext x
  change f x.val.1-g (degreeZero f g t v ht s hs x).2 = v (g (s (jet f g t v x)))
  rw [← h,division,map_sub,map_sub]
  have hx : f x.val.1=v (g x.val.2) := sub_eq_zero.mp x.property
  rw [hx]
  abel

include h in
/-- On the original cocycles, the chain map is literally inverse to the
coordinate-power inclusion. This fixes its H0 normalization. -/
lemma original_cocycle (x : LinearMap.ker (difference f g)) :
    degreeZero f g t v ht s hs (inclusion f g t v h x)=x.val := by
  apply Prod.ext
  · rfl
  · apply ht
    rw [division,jet_inclusion,map_zero,sub_zero]
    rfl

include h hs in
/-- The actual degree-one map descends to the SAME original connecting
map, independently of the chosen linear lift of jets. -/
lemma original_boundary (q : B ⧸ t.range) :
    (difference f g).range.mkQ (degreeOne g t v s q)=TwoChartJetCokernel318.connecting f g t v h q := by
  have hq := LinearMap.congr_fun hs q
  change t.range.mkQ (s q)=q at hq
  conv_rhs => rw [← hq]
  rfl

@[expose] def onKernel : LinearMap.ker (jet f g t v) →ₗ[R] LinearMap.ker (difference f g) :=
  ((degreeZero f g t v ht s hs).comp (LinearMap.ker (jet f g t v)).subtype).codRestrict _ (by
    intro x
    have hx := LinearMap.congr_fun (square f g t v h ht s hs) x.val
    change difference f g (degreeZero f g t v ht s hs x.val)=degreeOne g t v s (jet f g t v x.val) at hx
    rw [x.property,map_zero] at hx
    exact hx)

include h in
lemma onKernel_inverse (x : LinearMap.ker (difference f g)) :
    onKernel f g t v h ht s hs (kernelMap f g t v h x)=x := by
  apply Subtype.ext
  exact original_cocycle f g t v h ht s hs x

include h in
lemma onKernel_bijective : Function.Bijective (onKernel f g t v h ht s hs) := by
  constructor
  · intro x y hxy
    obtain ⟨a,rfl⟩ := kernelMap_surjective f g t v h x
    obtain ⟨b,rfl⟩ := kernelMap_surjective f g t v h y
    rw [onKernel_inverse,onKernel_inverse] at hxy
    rw [hxy]
  · intro x
    exact ⟨kernelMap f g t v h x,onKernel_inverse f g t v h ht s hs x⟩

/-- Induced degree-one map of this actual chain map. -/
@[expose] def onCokernel : ((B ⧸ t.range) ⧸ (jet f g t v).range) →ₗ[R]
    M ⧸ (difference f g).range :=
  (jet f g t v).range.liftQ ((difference f g).range.mkQ.comp (degreeOne g t v s)) (by
    rintro x ⟨k,rfl⟩
    change (difference f g).range.mkQ (degreeOne g t v s (jet f g t v k))=0
    have he := LinearMap.congr_fun (square f g t v h ht s hs) k
    change difference f g (degreeZero f g t v ht s hs k)=degreeOne g t v s (jet f g t v k) at he
    rw [← he,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact ⟨degreeZero f g t v ht s hs k,rfl⟩)

include h in
lemma onCokernel_eq : onCokernel f g t v h ht s hs = TwoChartJetCokernel318.quotientMap f g t v h := by
  ext q
  obtain ⟨x,rfl⟩ := (jet f g t v).range.mkQ_surjective q
  exact original_boundary f g t v h s hs x

include h in
lemma onCokernel_bijective (hp : Function.Surjective (positiveDifference f g v)) :
    Function.Bijective (onCokernel f g t v h ht s hs) := by
  rw [onCokernel_eq]
  exact (TwoChartJetCokernel318.equivalence f g t v h hp).bijective

/-- A linear jet lift exists because the ACTUAL jet quotient is projective,
not because arbitrary coefficient extension is left exact. -/
theorem exists_lift [Module.Projective R (B ⧸ t.range)] :
    ∃ s : (B ⧸ t.range) →ₗ[R] B, t.range.mkQ.comp s=LinearMap.id :=
  Module.projective_lifting_property t.range.mkQ LinearMap.id t.range.mkQ_surjective
end TwoChartJetChainMap318
