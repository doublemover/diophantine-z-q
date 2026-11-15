module
public import ProjectiveSectionIdeal318
public import OriginalAffineLineDualFrame318
public import OriginalCoefficientChartLine318
public section
noncomputable section
namespace OriginalAffineSectionZero318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : CommRingCat.{u}) (L : Line (Spec R))
local instance : Module.FinitePresentation R (OriginalLineAffineModel318.sections R L) :=
  (OriginalLineAffineModel318.properties R L).1

/-- Actual evaluation zero ideal of an ORIGINAL affine line section. -/
@[expose] def ideal (s : OriginalLineAffineModel318.sections R L) : Ideal R :=
  ProjectiveSectionIdeal318.ideal R _ s

/-- Actual quotient scheme cut out by the original section ideal. No
regularity, nonzero-divisor or Cartier-divisor claim is baked into it. -/
@[expose] def zeroScheme (s : OriginalLineAffineModel318.sections R L) : Scheme :=
  Spec (CommRingCat.of (R ⧸ ideal R L s))
@[expose] def into (s : OriginalLineAffineModel318.sections R L) : zeroScheme R L s ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal R L s)))

lemma ideal_eq_bot_iff (s : OriginalLineAffineModel318.sections R L) : ideal R L s=⊥ ↔ s=0 :=
  ProjectiveSectionIdeal318.ideal_eq_bot_iff R _ s

/-- The zero ideal follows the actual affine pullback/comparison unit
along any original specified line path. -/
lemma along_path {A B : CommRingCat.{u}} (f : A ⟶ B)
    (K : Line (Spec A)) (N : Line (Spec B))
    (e : (Scheme.Modules.pullback (Spec.map f)).obj K.object ≅ N.object)
    (s : OriginalLineAffineModel318.sections A K) :
    ideal B N (OriginalAffineLinePathSections318.restriction f K N e s)=
      Ideal.map f.hom (ideal A K s) := by
  letI : Algebra A B := f.hom.toAlgebra
  letI := (OriginalLineAffineModel318.properties A K).1
  have he := ProjectiveSectionIdeal318.base_change A
    (OriginalLineAffineModel318.sections A K) B (OriginalLineAffineModel318.sections B N)
    (OriginalAffineLinePathSections318.comparison f K N e).toLinearEquiv s
  have hu := OriginalAffineLinePathSections318.unit_apply f K N e s
  change (OriginalAffineLinePathSections318.comparison f K N e).toLinearEquiv ((1:B) ⊗ₜ[A] s)=
    OriginalAffineLinePathSections318.restriction f K N e s at hu
  rw [hu] at he
  exact he

variable {X Y : Scheme.{u}} (p : Y ⟶ X) {A B : CommRingCat.{u}}
  (f : A ⟶ B) (j : Spec A ⟶ X) (k : Spec B ⟶ Y)
  (h : Spec.map f ≫ j=k ≫ p) (N : Line X)
local instance : Algebra A B := f.hom.toAlgebra

/-- The zero ideal commutes with the ACTUAL original affine coefficient
pullback of the SAME line. It uses the genuine affine section-comparison
unit; no replacement of the section by a matching coordinate is assumed. -/
lemma original_pullback (s : OriginalLineAffineModel318.sections A (LineSheafPullback318.line j N)) :
    ideal B (LineSheafPullback318.line k (LineSheafPullback318.line p N))
      (OriginalCoefficientChartLine318.originalRestriction p f j k h N s)=
    Ideal.map f.hom (ideal A (LineSheafPullback318.line j N) s) := by
  letI := (OriginalLineAffineModel318.properties A (LineSheafPullback318.line j N)).1
  have he := ProjectiveSectionIdeal318.base_change A
    (OriginalLineAffineModel318.sections A (LineSheafPullback318.line j N)) B
    (OriginalLineAffineModel318.sections B (LineSheafPullback318.line k (LineSheafPullback318.line p N)))
    (OriginalCoefficientChartLine318.sectionsComparison p f j k h N).toLinearEquiv s
  have hu := OriginalCoefficientChartLine318.unit p f j k h N s
  change (OriginalCoefficientChartLine318.sectionsComparison p f j k h N).toLinearEquiv
    ((1:B) ⊗ₜ[A] s)=OriginalCoefficientChartLine318.originalRestriction p f j k h N s at hu
  rw [hu] at he
  exact he
end OriginalAffineSectionZero318
