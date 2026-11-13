module
public import SchemeOpenPullbackPointsRebuild318
public section
noncomputable section
namespace SchemeOpenRangePullbackRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {N S V Z : Scheme.{u}} (j : N ⟶ S) (m : N ⟶ V) (n : S ⟶ Z) (i : V ⟶ Z)
  [IsOpenImmersion j] [Mono i]
/-- A source open with the EXACT inverse-image range and a commuting
square is the actual categorical pullback, including all nonreduced tests. -/
lemma square (w : j ≫ n=m ≫ i)
    (h : Set.range j=n ⁻¹' Set.range i) : IsPullback j m n i := by
  let lift (s : PullbackCone n i) : s.pt ⟶ N := IsOpenImmersion.lift j s.fst (by
    rw [h]
    rintro _ ⟨x,rfl⟩
    exact ⟨s.snd x,(congrArg (fun q => q x) s.condition).symm⟩)
  have first (s : PullbackCone n i) : lift s ≫ j=s.fst := IsOpenImmersion.lift_fac _ _ _
  have second (s : PullbackCone n i) : lift s ≫ m=s.snd := by
    apply (cancel_mono i).mp
    rw [Category.assoc,←w,←Category.assoc,first,s.condition]
  apply IsPullback.of_isLimit' ⟨w⟩
  refine PullbackCone.IsLimit.mk _ lift first second ?_
  intro s a ha _
  exact (cancel_mono j).mp (ha.trans (first s).symm)
end SchemeOpenRangePullbackRebuild318
