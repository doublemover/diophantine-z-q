module
public import ProjectiveRatioOverlapEquations318
public section
noncomputable section
namespace ProjectiveSubopenRatioAtlas318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
open ProjectivePreimageRegularRatios318
variable {ι : Type*} {X : Scheme} [IsReduced X]
local instance standardGrading : GradedAlgebra (grading (ι := ι)) := MvPolynomial.gradedAlgebra
variable (f : X ⟶ Proj (grading (ι := ι)))

/-- Restrict an already constructed regular target ratio to an actual
source subopen. This is a whole ring section, not an evaluation function. -/
@[expose] def ratio (U : X.Opens) (j : ι) (h : U ≤ sourceOpen f j) (i : ι) : Γ(U.toScheme,⊤) :=
  (X.homOfLE h).appTop (ratioSection f j i)

lemma ratio_self (U : X.Opens) (j : ι) (h : U ≤ sourceOpen f j) : ratio f U j h j = 1 := by
  rw [ratio,ProjectivePreimageRegularRatios318.ratio_self,map_one]

/-- Literal composition of actual restriction morphisms, used before
transporting any regular-function equation to smaller overlaps. -/
lemma restriction_comp {U V Z : X.Opens} (hUV : U ≤ V) (hVZ : V ≤ Z) :
    X.homOfLE hUV ≫ X.homOfLE hVZ = X.homOfLE (hUV.trans hVZ) := by
  apply (cancel_mono Z.ι).1
  simp only [Category.assoc,Scheme.homOfLE_ι]

lemma ratio_restrict {U V : X.Opens} (hUV : U ≤ V) (j i : ι)
    (hV : V ≤ sourceOpen f j) :
    (X.homOfLE hUV).appTop (ratio f V j hV i) = ratio f U j (hUV.trans hV) i := by
  change (X.homOfLE hUV ≫ X.homOfLE hV).appTop (ratioSection f j i) = _
  rw [restriction_comp]
  rfl

variable (π : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType π]
  (hf : f ≫ ComplexProjectiveBase318.structureMap = π)
  (hpoints : ∀ p : Spec (CommRingCat.of ℂ) ⟶ X, p ≫ π = 𝟙 _ →
    ∃ v : ι → ℂ, ∃ hv : ∃ i,v i≠0, p ≫ f = ComplexProjectiveSchemePoint318.point v hv)
include π hf hpoints

/-- Exact transition on ANY smaller scheme open, so common refinements
of unrelated projective atlases need no new pointwise argument. -/
theorem transition (U : X.Opens) (j k i : ι)
    (hj : U ≤ sourceOpen f j) (hk : U ≤ sourceOpen f k) :
    ratio f U j hj i = ratio f U k hk i * ratio f U j hj k := by
  let h : U ≤ sourceOpen f j ⊓ sourceOpen f k := le_inf hj hk
  have he := congrArg ((X.homOfLE h).appTop)
    (ProjectiveRatioOverlapEquations318.transition f π hf hpoints j k i)
  rw [map_mul] at he
  change (X.homOfLE h ≫ ProjectiveRatioOverlapEquations318.left f j k).appTop
      (ratioSection f j i) =
    (X.homOfLE h ≫ ProjectiveRatioOverlapEquations318.right f j k).appTop
      (ratioSection f k i) *
    (X.homOfLE h ≫ ProjectiveRatioOverlapEquations318.left f j k).appTop
      (ratioSection f j k) at he
  simpa only [ProjectiveRatioOverlapEquations318.left,ProjectiveRatioOverlapEquations318.right,
    restriction_comp,ratio] using he

theorem transition_isUnit (U : X.Opens) (j k : ι)
    (hj : U ≤ sourceOpen f j) (hk : U ≤ sourceOpen f k) :
    IsUnit (ratio f U j hj k) := by
  let h : U ≤ sourceOpen f j ⊓ sourceOpen f k := le_inf hj hk
  have hu := (ProjectiveRatioOverlapEquations318.transition_isUnit f π hf hpoints j k).map
    (X.homOfLE h).appTop
  change IsUnit ((X.homOfLE h ≫ ProjectiveRatioOverlapEquations318.left f j k).appTop
    (ratioSection f j k)) at hu
  simpa only [ProjectiveRatioOverlapEquations318.left,restriction_comp,ratio] using hu
end ProjectiveSubopenRatioAtlas318
