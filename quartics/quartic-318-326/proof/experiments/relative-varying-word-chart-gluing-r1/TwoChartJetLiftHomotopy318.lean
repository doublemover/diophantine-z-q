module
public import TwoChartJetChainMap318
public section
noncomputable section
namespace TwoChartJetLiftHomotopy318
open TwoChartJetDifferential318 TwoChartJetChainMap318
universe u v w z
variable {R : Type u} [CommRing R]
  {A : Type v} [AddCommGroup A] [Module R A]
  {B : Type w} [AddCommGroup B] [Module R B]
  {M : Type z} [AddCommGroup M] [Module R M]
  (f : A →ₗ[R] M) (g : B →ₗ[R] M) (t : B →ₗ[R] B) (v : M ≃ₗ[R] M)
  (h : ∀ b, v (g (t b))=g b) (ht : Function.Injective t)
  (s s' : (B ⧸ t.range) →ₗ[R] B)
  (hs : t.range.mkQ.comp s=LinearMap.id) (hs' : t.range.mkQ.comp s'=LinearMap.id)

/-- The difference of two actual jet lifts lies in the ORIGINAL
coordinate-power image, even over a nonreduced coefficient ring. -/
@[expose] def liftDifference : (B ⧸ t.range) →ₗ[R] t.range :=
  (s'-s).codRestrict _ (by
    intro q
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change t.range.mkQ (s' q-s q)=0
    rw [map_sub]
    have h0 := LinearMap.congr_fun hs q
    have h1 := LinearMap.congr_fun hs' q
    change t.range.mkQ (s q)=q at h0
    change t.range.mkQ (s' q)=q at h1
    rw [h0,h1,sub_self])

/-- Explicit two-term chain homotopy, zero on the finite coordinate and
literal coordinate-power division on the difference of infinity lifts. -/
@[expose] def homotopy : (B ⧸ t.range) →ₗ[R] A × B :=
  (0 : (B ⧸ t.range) →ₗ[R] A).prod
    ((ontoRange t ht).symm.toLinearMap.comp (liftDifference t s s' hs hs'))

lemma power_homotopy (q : B ⧸ t.range) :
    t (homotopy (A := A) t ht s s' hs hs' q).2=s' q-s q :=
  congrArg Subtype.val ((ontoRange t ht).apply_symm_apply (liftDifference t s s' hs hs' q))

/-- Degree zero of F_s-F_s' is H∘d, for the unchanged finite jet differential. -/
lemma zero_square : degreeZero f g t v ht s hs-degreeZero f g t v ht s' hs' =
    (homotopy (A := A) t ht s s' hs hs').comp (jet f g t v) := by
  ext x
  apply Prod.ext
  · change x.val.1-x.val.1=0
    exact sub_self _
  · apply ht
    change t ((degreeZero f g t v ht s hs x).2-(degreeZero f g t v ht s' hs' x).2)=_
    rw [map_sub,division,division,power_homotopy]
    abel

include h in
/-- Degree one of F_s-F_s' is d∘H. Thus the original Cech comparison is
independent of the chosen projective jet lift UP TO ACTUAL CHAIN HOMOTOPY. -/
lemma one_square : degreeOne g t v s-degreeOne g t v s' =
    (difference f g).comp (homotopy (A := A) t ht s s' hs hs') := by
  ext q
  change v (g (s q))-v (g (s' q))=f 0-g (homotopy (A := A) t ht s s' hs hs' q).2
  rw [map_zero,zero_sub,← h,power_homotopy,map_sub,map_sub]
  abel
end TwoChartJetLiftHomotopy318
