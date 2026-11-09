module
public import ContactZariskiClassDescent318
public import Mathlib.CategoryTheory.Sites.Over
public section
noncomputable section
namespace OriginalRelativeSite318
open AlgebraicGeometry CategoryTheory Opposite
open RelativeLineClassBaseChange318
universe u
variable {C B : Scheme.{u}} (q : C ⟶ B)

/-- The literal underlying-type presheaf of the original relative groups
on the actual category of schemes over their original base. -/
@[expose] def presheaf : (Over B)ᵒᵖ ⥤ Type (u+1) :=
  RelativeLineClassBaseChange318.presheaf q ⋙ forget CommGrpCat

abbrev object {T : Scheme.{u}} (b : T ⟶ B) : Over B := Over.mk b
abbrev arrow {T T' : Scheme.{u}} (b : T ⟶ B) (b' : T' ⟶ B)
    (g : T' ⟶ T) (hg : g ≫ b = b') : object b' ⟶ object b := Over.homMk g hg

lemma map_apply {T T' : Scheme.{u}} (b : T ⟶ B) (b' : T' ⟶ B)
    (g : T' ⟶ T) (hg : g ≫ b = b') (c : TestClass q b) :
    (presheaf q).map (arrow b b' g hg).op c = testMap q b b' g hg c := rfl

/-- Actual open subtests are objects of the same relative site. -/
abbrev openObject {T : Scheme.{u}} (b : T ⟶ B) (U : T.Opens) : Over B :=
  object (U.ι ≫ b)
abbrev openArrow {T : Scheme.{u}} (b : T ⟶ B) (U : T.Opens) : openObject b U ⟶ object b :=
  arrow b (U.ι ≫ b) U.ι rfl
abbrev openInclusion {T : Scheme.{u}} (b : T ⟶ B) {U V : T.Opens} (h : V ≤ U) :
    openObject b V ⟶ openObject b U :=
  arrow (U.ι ≫ b) (V.ι ≫ b) (T.homOfLE h) (OriginalOpenTestNaturality318.test_path b h)

lemma openInclusion_arrow {T : Scheme.{u}} (b : T ⟶ B) {U V : T.Opens} (h : V ≤ U) :
    openInclusion b h ≫ openArrow b U = openArrow b V := by
  ext
  exact Scheme.homOfLE_ι _ _
/-- Membership of an arbitrary original relative arrow is detected by
its literal underlying scheme arrow under the standard sieve equivalence. -/
lemma sieve_mem_left {Y Z : Over B} (R : Sieve Y) (g : Z ⟶ Y) :
    R g ↔ Sieve.overEquiv Y R g.left := by
  change R g ↔ ((R.functorPushforward (Over.forget B)).functorPullback (Over.forget B)) g
  rw [Sieve.functorPullback_functorPushforward_overForget]
end OriginalRelativeSite318
