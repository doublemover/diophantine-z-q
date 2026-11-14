module
public import ContactBoundedCartierDivisorChange318
public section
noncomputable section
namespace ContactBoundedCartierAbelNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B T : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (g : T ⟶ B) (hg : g ≫ b=t) (D : ContactBoundedCartierEquiv318.Data c N b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
@[expose] def value : (RelativeFppfLineSheaf318.sheaf p).obj.obj (op (Over.mk b)) :=
  (RelativeFppfLineSheaf318.unit p).app (op (Over.mk b))
    (OriginalLineAbelTransformation318.point p b (ContactBoundedCartierAbel318.divisorLine c N b D))
/-- The original all-test Abel value of the whole base-changed divisor
is the evaluation of the SAME original Abel transformation at that test. -/
lemma test_value : value c N t (ContactBoundedCartierBaseChange318.map c N b t g hg D)=
    (ContactBoundedCartierAbel318.transformation c N b D).app (op (Over.mk t))
      (Over.homMk g hg) := by
  change (RelativeFppfLineSheaf318.unit p).app (op (Over.mk t))
    (OriginalLineAbelTransformation318.point p t
      (ContactBoundedCartierAbel318.divisorLine c N t (ContactBoundedCartierBaseChange318.map c N b t g hg D)))=_
  rw [ContactBoundedCartierDivisorChange318.relative_class]
  rfl
/-- Genuine all-scheme naturality into the actual associated fppf line
sheaf. No representability or injectivity of sheafification is assumed. -/
lemma natural : (RelativeFppfLineSheaf318.sheaf p).obj.map (Over.homMk g hg).op
    (value c N b D)=value c N t (ContactBoundedCartierBaseChange318.map c N b t g hg D) := by
  have hn := ConcreteCategory.congr_hom ((RelativeFppfLineSheaf318.unit p).naturality (Over.homMk g hg).op)
    (OriginalLineAbelTransformation318.point p b (ContactBoundedCartierAbel318.divisorLine c N b D))
  change (RelativeFppfLineSheaf318.unit p).app (op (Over.mk t))
    (RelativeLineClassBaseChange318.testMap p b t g hg
      (OriginalLineAbelTransformation318.point p b (ContactBoundedCartierAbel318.divisorLine c N b D)))=
    (RelativeFppfLineSheaf318.sheaf p).obj.map (Over.homMk g hg).op (value c N b D) at hn
  rw [← ContactBoundedCartierDivisorChange318.relative_class] at hn
  exact hn.symm
end ContactBoundedCartierAbelNaturality318
