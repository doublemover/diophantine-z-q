module
public import RegularClosedFlatPullback318
public section
noncomputable section
namespace RegularClosedBaseCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X B : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (a : X ⟶ B) (U : B.OpenCover)
/-- Checking the actual whole closed family on an entire coefficient
open cover checks its genuine Cartier charts on the whole ambient. -/
lemma regular (h : ∀ i,OriginalRegularClosedCharts318.Property
    (ClosedFamilyBaseRestriction318.into a p (U.f i))) :
    OriginalRegularClosedCharts318.Property p := by
  apply OriginalRegularClosedCharts318.glue p
    (fun i => pullback a (U.f i))
    (fun i => ClosedFamilyBaseRestriction318.family a p (U.f i))
    (fun i => pullback.fst a (U.f i))
    (fun i => ClosedFamilyBaseRestriction318.into a p (U.f i))
    (fun i => ClosedFamilyBaseRestriction318.toFamily a p (U.f i))
  · intro i
    infer_instance
  · intro x
    obtain ⟨i,y,hy⟩ := (U.pullback₁ a).exists_eq x
    exact ⟨i,y,hy⟩
  · intro i
    exact (ClosedFamilyBaseRestriction318.cartesian a p (U.f i)).flip
  · exact h
end RegularClosedBaseCover318
