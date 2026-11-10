module
public import TwoChartJetDifferential318
public section
noncomputable section
namespace TwoChartJetCokernel318
open TwoChartJetDifferential318
universe u v w z
variable {R : Type u} [CommRing R]
  {A : Type v} [AddCommGroup A] [Module R A]
  {B : Type w} [AddCommGroup B] [Module R B]
  {M : Type z} [AddCommGroup M] [Module R M]
  (f : A →ₗ[R] M) (g : B →ₗ[R] M) (t : B →ₗ[R] B) (v : M ≃ₗ[R] M)
  (h : ∀ b, v (g (t b))=g b)

@[expose] def connecting : (B ⧸ t.range) →ₗ[R] M ⧸ (difference f g).range :=
  t.range.liftQ ((difference f g).range.mkQ.comp (v.toLinearMap.comp g)) (by
    rintro x ⟨b,rfl⟩
    change (difference f g).range.mkQ (v (g (t b)))=0
    rw [h,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact ⟨(0,-b),by simp [difference]⟩)

include h in
lemma jet_connecting_zero (x : LinearMap.ker (positiveDifference f g v)) :
    connecting f g t v h (jet f g t v x)=0 := by
  change (difference f g).range.mkQ (v (g x.val.2))=0
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  refine ⟨(x.val.1,0),?_⟩
  have hx : f x.val.1-v (g x.val.2)=0 := x.property
  simpa only [difference,LinearMap.sub_apply,LinearMap.comp_apply,
    LinearMap.fst_apply,LinearMap.snd_apply,map_zero,sub_zero] using sub_eq_zero.mp hx

include h in
lemma kernel : LinearMap.ker (connecting f g t v h) = (jet f g t v).range := by
  ext q
  constructor
  · intro hq
    obtain ⟨b,rfl⟩ := t.range.mkQ_surjective q
    have hb : v (g b) ∈ (difference f g).range := by
      change (difference f g).range.mkQ (v (g b))=0 at hq
      exact (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨⟨a,y⟩,hy⟩ := hb
    have he : f a-g y=v (g b) := hy
    have hk : f a-v (g (b+t y))=0 := by
      rw [map_add,map_add,h]
      exact sub_eq_zero.mpr (eq_add_of_sub_eq he)
    refine ⟨⟨(a,b+t y),hk⟩,?_⟩
    change t.range.mkQ (b+t y)=t.range.mkQ b
    rw [map_add]
    have hz : t.range.mkQ (t y)=0 := by
      rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      exact ⟨y,rfl⟩
    rw [hz,add_zero]
  · rintro ⟨x,rfl⟩
    exact jet_connecting_zero f g t v h x

include h in
lemma surjective (hs : Function.Surjective (positiveDifference f g v)) :
    Function.Surjective (connecting f g t v h) := by
  intro q
  obtain ⟨m,rfl⟩ := (difference f g).range.mkQ_surjective q
  obtain ⟨⟨a,b⟩,hab⟩ := hs m
  refine ⟨t.range.mkQ (-b),?_⟩
  change (difference f g).range.mkQ (v (g (-b)))=(difference f g).range.mkQ m
  have ha : (difference f g).range.mkQ (f a)=0 := by
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact ⟨(a,0),by simp [difference]⟩
  change f a-v (g b)=m at hab
  rw [← hab,map_sub,ha,zero_sub,map_neg,map_neg,map_neg]

/-- The actual jet cokernel is the original SAME-chart Cech cokernel.
Only surjectivity of the positive differential is used; no exactness of
tensoring or finite-kernel theorem is assumed. -/
@[expose] def quotientMap : ((B ⧸ t.range) ⧸ (jet f g t v).range) →ₗ[R]
    M ⧸ (difference f g).range :=
  (jet f g t v).range.liftQ (connecting f g t v h) (by
    rw [kernel f g t v h])

include h in
lemma quotientMap_injective : Function.Injective (quotientMap f g t v h) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro q hq
  change q=0
  obtain ⟨x,rfl⟩ := (jet f g t v).range.mkQ_surjective q
  change connecting f g t v h x=0 at hq
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  have hx : x ∈ LinearMap.ker (connecting f g t v h) := hq
  rw [kernel] at hx
  exact hx

@[expose] def equivalence (hs : Function.Surjective (positiveDifference f g v)) :
    ((B ⧸ t.range) ⧸ (jet f g t v).range) ≃ₗ[R] M ⧸ (difference f g).range :=
  LinearEquiv.ofBijective (quotientMap f g t v h) ⟨quotientMap_injective f g t v h,by
    intro q
    obtain ⟨x,hx⟩ := surjective f g t v h hs q
    exact ⟨(jet f g t v).range.mkQ x,hx⟩⟩
end TwoChartJetCokernel318
