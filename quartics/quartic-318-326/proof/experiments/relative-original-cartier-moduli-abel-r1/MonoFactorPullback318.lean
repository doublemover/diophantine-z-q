module
public import ContactQuotientUniversalOverlapIso318
public section
noncomputable section
namespace MonoFactorPullback318
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] {V A B U X : C}
  (l : V ⟶ A) (r : V ⟶ B) (q : A ⟶ U) (j : U ⟶ X) (f : B ⟶ X) [Mono q]
/-- A genuine chart-restriction pullback whose other leg factors through
a monomorphic local quotient is the actual quotient-family intersection. -/
lemma square (H : IsPullback r (l ≫ q) f j) : IsPullback l r (q ≫ j) f := by
  have w : l ≫ (q ≫ j)=r ≫ f := by simpa only [Category.assoc] using H.w.symm
  let lift (s : PullbackCone (q ≫ j) f) : s.pt ⟶ V :=
    H.lift s.snd (s.fst ≫ q) (by simpa only [Category.assoc] using s.condition.symm)
  apply IsPullback.of_isLimit' ⟨w⟩
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro s
    apply (cancel_mono q).mp
    simpa only [Category.assoc] using H.lift_snd s.snd (s.fst ≫ q) _
  · intro s
    exact H.lift_fst _ _ _
  · intro s a ha hb
    apply H.hom_ext
    · exact hb.trans (H.lift_fst _ _ _).symm
    · calc
        a ≫ (l ≫ q) = s.fst ≫ q := by rw [← Category.assoc,ha]
        _ = lift s ≫ (l ≫ q) := (H.lift_snd _ _ _).symm
end MonoFactorPullback318
