module
public import PrincipalFrameZeroScheme318
public import PrincipalZeroUniversal318
public import OpenPointScalarPullback318
public section
noncomputable section
namespace FramedZeroUniversalData318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

/-- Actual regular frame coefficients on a full open cover, with their
whole unit transition identity. No test-scheme factorization is assumed. -/
structure Data (X : Scheme.{u}) where
  Index : Type u
  opens : Index → X.Opens
  coefficient : ∀ i,Γ(X,opens i)
  transition : ∀ i j,Γ(X,opens i ⊓ opens j)ˣ
  compatible : ∀ i j,X.presheaf.map (homOfLE inf_le_left).op (coefficient i)=
    (transition i j).val*X.presheaf.map (homOfLE inf_le_right).op (coefficient j)
  covers : (⊤ : X.Opens)≤⨆ i,opens i
variable {X T : Scheme.{u}} (D : Data X)
abbrev Zero := PrincipalFrameZeroScheme318.scheme D.opens D.coefficient D.transition D.compatible
abbrev inclusion : D.Zero ⟶ X := PrincipalFrameZeroScheme318.inclusion
  D.opens D.coefficient D.transition D.compatible
instance closed : IsClosedImmersion D.inclusion := PrincipalFrameZeroScheme318.closed
  D.opens D.coefficient D.transition D.compatible D.covers
abbrev equation (i : D.Index) := PrincipalFrameZeroOverlaps318.coefficient D.opens D.coefficient i
abbrev localZero (i : D.Index) := PrincipalIdealOpenRestriction318.zeroScheme (D.equation i)
abbrev localInclusion (i : D.Index) : D.localZero i ⟶ (D.opens i).toScheme :=
  PrincipalIdealOpenRestriction318.inclusion (D.equation i)
abbrev chart (i : D.Index) : D.localZero i ⟶ D.Zero := PrincipalFrameZeroScheme318.chart
  D.opens D.coefficient D.transition D.compatible i
lemma cartesian (i : D.Index) : IsPullback (D.localInclusion i) (D.chart i) (D.opens i).ι D.inclusion :=
  PrincipalFrameZeroScheme318.cartesian D.opens D.coefficient D.transition D.compatible i
@[reassoc] lemma chart_inclusion (i : D.Index) : D.chart i≫D.inclusion=D.localInclusion i≫(D.opens i).ι :=
  (D.cartesian i).w.symm

/-- Literal vanishing of the pulled-back regular coefficients. This is
an equation in full section rings of the arbitrary test scheme. -/
@[expose] def Vanishing (f : T ⟶ X) : Prop := ∀ i,f.app (D.opens i) (D.coefficient i)=0
@[expose] def testOpen (f : T ⟶ X) (i : D.Index) := f ⁻¹ᵁ D.opens i
lemma test_covers (f : T ⟶ X) : (⊤ : T.Opens)≤⨆ i,D.testOpen f i := by
  intro x hx
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (D.covers (show f x∈⊤ from trivial))
  exact Opens.mem_iSup.mpr ⟨i,hi⟩
@[expose] def testCover (f : T ⟶ X) : T.OpenCover :=
  ClosedSubschemeCoverGluing318.ambientCover (D.testOpen f) (D.test_covers f)
abbrev restriction (f : T ⟶ X) (i : D.Index) : (D.testOpen f i).toScheme ⟶ (D.opens i).toScheme :=
  f.resLE (D.opens i) (D.testOpen f i) le_rfl
lemma restriction_equation (f : T ⟶ X) (i : D.Index) :
    (D.restriction f i).appTop (D.equation i)=
      (LineFrameTopScalar318.ringTop (D.testOpen f i)).inv (f.app (D.opens i) (D.coefficient i)) :=
  OpenPointScalarPullback318.restriction_square f (D.opens i) (D.coefficient i)
end FramedZeroUniversalData318
