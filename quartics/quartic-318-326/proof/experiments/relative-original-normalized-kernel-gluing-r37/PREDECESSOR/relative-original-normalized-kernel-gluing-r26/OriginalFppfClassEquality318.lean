module
public import OriginalFppfUnitLocalInjective318
public section
noncomputable section
namespace OriginalFppfClassEquality318
open AlgebraicGeometry CategoryTheory Opposite
variable {X S : Scheme.{0}} (p : X ⟶ S) (B : Over S)
  (x y : (RelativeLineClassBaseChange318.presheaf p).obj (op B))
/-- Actual associated-sheaf equality is exactly a covering naive
equalizer sieve, not global injectivity of the unit. -/
lemma iff_covering : (RelativeFppfLineSheaf318.unit p).app (op B) x=
    (RelativeFppfLineSheaf318.unit p).app (op B) y ↔
      Presheaf.equalizerSieve x y ∈ RelativeFppfLineSheaf318.topology S B := by
  constructor
  · exact Presheaf.equalizerSieve_mem _ (RelativeFppfLineSheaf318.unit p) x y
  · intro h
    have hf : Presheaf.IsSheaf (RelativeFppfLineSheaf318.topology S)
        ((RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1}) :=
      (Presheaf.isSheaf_iff_isSheaf_forget (forget CommGrpCat.{1})).mp (RelativeFppfLineSheaf318.sheaf p).property
    have ht := (isSheaf_iff_isSheaf_of_type _ _).mp hf
    apply (ht.isSeparated _ h).ext
    intro T f he
    have hx := ConcreteCategory.congr_hom ((RelativeFppfLineSheaf318.unit p).naturality f.op) x
    have hy := ConcreteCategory.congr_hom ((RelativeFppfLineSheaf318.unit p).naturality f.op) y
    change (RelativeLineClassBaseChange318.presheaf p).map f.op x=
      (RelativeLineClassBaseChange318.presheaf p).map f.op y at he
    exact hx.symm.trans ((congrArg ((RelativeFppfLineSheaf318.unit p).app (op T)) he).trans hy)
end OriginalFppfClassEquality318
