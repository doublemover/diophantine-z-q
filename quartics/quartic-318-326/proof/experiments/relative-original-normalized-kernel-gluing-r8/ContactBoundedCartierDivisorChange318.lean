module
public import CartierDivisorLineBaseChange318
public section
noncomputable section
namespace ContactBoundedCartierDivisorChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B T : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (g : T ⟶ B) (hg : g ≫ b=t) (D : ContactBoundedCartierEquiv318.Data c N b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "m" => RelativeSchemeCoefficient318.map p b t g hg
local notation "D'" => ContactBoundedCartierBaseChange318.map c N b t g hg D
/-- The actual original bounded divisor line follows the literal full
ideal coefficient operation on ALL scheme tests. -/
lemma divisor_class : classOf (ContactBoundedCartierAbel318.divisorLine c N t D')=
    classOf (LineSheafPullback318.line m (ContactBoundedCartierAbel318.divisorLine c N b D)) :=
  CartierDivisorLineBaseChange318.divisor_class D.val.ideal.subschemeι (pullback.snd p b) g
    D'.val.ideal.subschemeι (IdealSheafCoefficientCartesian318.map D.val.ideal m) m (pullback.snd p t)
    (IdealSheafCoefficientCartesian318.cartesian D.val.ideal m)
    (RelativeSchemeCoefficient318.cartesian p b t g hg) D.property
@[expose] def divisorIso : (ContactBoundedCartierAbel318.divisorLine c N t D').object ≅
    (LineSheafPullback318.line m (ContactBoundedCartierAbel318.divisorLine c N b D)).object :=
  Classical.choice ((classOf_eq_iff _ _).mp (divisor_class c N b t g hg D))
lemma totalMap : RelativeLineClassBaseChange318.totalMap p b t g hg=m := rfl
/-- Actual naive relative O(D) classes commute with every coefficient
map before fppf sheafification, not just on field-valued points. -/
lemma relative_class : OriginalLineAbelTransformation318.point p t
    (ContactBoundedCartierAbel318.divisorLine c N t D')=
    RelativeLineClassBaseChange318.testMap p b t g hg
      (OriginalLineAbelTransformation318.point p b (ContactBoundedCartierAbel318.divisorLine c N b D)) := by
  change RelativeLineClassQuotient318.classMap (pullback.snd p t)
    (classOf (ContactBoundedCartierAbel318.divisorLine c N t D'))=_
  rw [RelativeLineClassBaseChange318.testMap_class,totalMap,divisor_class]
  rfl
end ContactBoundedCartierDivisorChange318
