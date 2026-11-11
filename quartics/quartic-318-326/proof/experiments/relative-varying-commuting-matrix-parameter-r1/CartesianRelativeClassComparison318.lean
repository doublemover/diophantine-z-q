module
public import LineClassIsoCancellation318
public import RelativeAmbientCharts318
public import RelativeLineClassBaseChange318
public section
noncomputable section
namespace CartesianRelativeClassComparison318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
universe u
variable {C S B T A : Scheme.{u}} (p : C ⟶ S) (b : B ⟶ S) (j : T ⟶ B)
  (a : A ⟶ C) (d : A ⟶ T) (h : IsPullback a d p (j ≫ b))
local notation "e" => h.isoPullback
local notation "t" => RelativeLineClassBaseChange318.totalMap p b (j ≫ b) j rfl
local notation "lift" => RelativeAmbientCharts318.lift p b j a d h

lemma comparison_total : e.hom ≫ t=lift := by
  apply pullback.hom_ext
  · simp only [Category.assoc,RelativeLineClassBaseChange318.totalMap_fst,
      h.isoPullback_hom_fst,RelativeAmbientCharts318.lift_original]
  · simp only [Category.assoc,RelativeLineClassBaseChange318.totalMap_snd,
      h.isoPullback_hom_snd_assoc,RelativeAmbientCharts318.lift_projection]

/-- A line comparison on the SPECIFIED actual Cartesian chart becomes
an equality on the standard fiber product used by the relative class
presheaf. No model isomorphism or pullback equivalence is omitted. -/
lemma class_on_test (D : Class (pullback p b)) (L : Class C)
    (he : LineClassPullbackHom318.pullback lift D=LineClassPullbackHom318.pullback a L) :
    LineClassPullbackHom318.pullback t D=
      LineClassPullbackHom318.pullback (pullback.fst p (j ≫ b)) L := by
  apply LineClassIsoCancellation318.injective e
  change LineClassPullbackHom318.pullback e.hom (LineClassPullbackHom318.pullback t D)=_
  rw [← MonoidHom.comp_apply,← LineClassPullbackHom318.composition,comparison_total]
  rw [← MonoidHom.comp_apply,← LineClassPullbackHom318.composition,h.isoPullback_hom_fst]
  exact he

lemma relative_on_test (D : Class (pullback p b)) (L : Class C)
    (he : LineClassPullbackHom318.pullback lift D=LineClassPullbackHom318.pullback a L) :
    RelativeLineClassBaseChange318.testMap p b (j ≫ b) j rfl
      (RelativeLineClassQuotient318.classMap (pullback.snd p b) D)=
    RelativeLineClassQuotient318.classMap (pullback.snd p (j ≫ b))
      (LineClassPullbackHom318.pullback (pullback.fst p (j ≫ b)) L) := by
  rw [RelativeLineClassBaseChange318.testMap_class,class_on_test p b j a d h D L he]
end CartesianRelativeClassComparison318
