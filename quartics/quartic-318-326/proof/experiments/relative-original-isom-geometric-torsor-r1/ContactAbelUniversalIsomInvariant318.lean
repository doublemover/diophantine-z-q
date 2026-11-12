module
public import ContactWholeGeometricKernelDescent318
public section
noncomputable section
namespace ContactAbelUniversalIsomInvariant318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "A" => ContactCartierDifferencePresheaf318.presheaf c
local notation "v" => ContactCartierDifferenceAbel318.transformation c
/-- The actual original Abel transformation is constant on each SAME
universal geometric Isom projection. This consumes actual universal
original line equality, not the quotient mapping property being proved. -/
lemma invariant : ContactGeometricIsomInvariant318.Invariant c
    (ContactDifferenceSheafEpimorphism318.target c) v := by
  intro R hR D E
  letI := hR
  let B := Over.mk (baseMap R)
  let L := ContactDifferenceNaiveClass318.line c B D
  let K := ContactDifferenceNaiveClass318.line c B E
  let π := ContactRelationProjectionImage318.projection R c L K
  let V := OriginalAbsoluteLinePresheaf318.value (ContactIntrinsicDifferentials318.structureMap c)
  have hd : V.app (op B) (classOf L)=v.app (op B) D :=
    ContactDifferenceNaiveClass318.sheaf_value c B D
  have he : V.app (op B) (classOf K)=v.app (op B) E :=
    ContactDifferenceNaiveClass318.sheaf_value c B E
  have hx := ConcreteCategory.congr_hom (V.naturality π.op) (classOf L)
  have hy := ConcreteCategory.congr_hom (V.naturality π.op) (classOf K)
  rw [hd] at hx
  rw [he] at hy
  exact hx.symm.trans ((ContactPicardGeometricCoverCriterion318.universal_equality R c L K).trans hy)
/-- Every map FROM the original Picard sheaf necessarily respects the
constructed geometric Isom schemes, on whole parameter objects. -/
lemma of_factor (F : Sheaf J (Type 1)) (a : A ⟶ F.obj)
    (g : ContactDifferenceSheafEpimorphism318.target c ⟶ F) (hg : v ≫ g.hom=a) :
    ContactGeometricIsomInvariant318.Invariant c F a := by
  intro R hR D E
  letI := hR
  let B := Over.mk (baseMap R)
  let π := ContactRelationProjectionImage318.projection R c
    (ContactDifferenceNaiveClass318.line c B D) (ContactDifferenceNaiveClass318.line c B E)
  have hd := ConcreteCategory.congr_hom (congrArg (fun n => n.app (op B)) hg) D
  have he := ConcreteCategory.congr_hom (congrArg (fun n => n.app (op B)) hg) E
  have hx := ConcreteCategory.congr_hom (g.hom.naturality π.op) (v.app (op B) D)
  have hy := ConcreteCategory.congr_hom (g.hom.naturality π.op) (v.app (op B) E)
  change g.hom.app (op B) (v.app (op B) D)=a.app (op B) D at hd
  change g.hom.app (op B) (v.app (op B) E)=a.app (op B) E at he
  rw [←hd,←he]
  exact hx.symm.trans ((congrArg (g.hom.app _)
    (invariant c R hR D E)).trans hy)
end ContactAbelUniversalIsomInvariant318
