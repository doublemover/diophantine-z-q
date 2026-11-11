module
public import RelativeCartierSchemeBaseChange318
public section
noncomputable section
namespace RelativeCartierSchemeCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X W Y B T : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (a : X ⟶ B) [hflat : Flat (p ≫ a)] (f : T ⟶ B)
  (q : W ⟶ Y) (t : W ⟶ Z) (g : Y ⟶ X) (b : Y ⟶ T)
  (F : IsPullback t q p g) (K : IsPullback g b a f)
include F K hflat in
/-- The all-scheme Cartier coefficient theorem applies to ANY actual
Cartesian closed-family model, including canonical full ideal comaps. -/
lemma regular (h : OriginalRegularClosedCharts318.Property p) :
    OriginalRegularClosedCharts318.Property q :=
  ClosedFamilyCartesianModel318.regular p a f q t g b F K
    (RelativeCartierSchemeBaseChange318.regular p a f h)
end RelativeCartierSchemeCartesian318
