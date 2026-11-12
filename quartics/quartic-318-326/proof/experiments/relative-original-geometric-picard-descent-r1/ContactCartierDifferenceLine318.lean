module
public import ContactCartierDifferenceAbel318
public section
noncomputable section
namespace ContactCartierDifferenceLine318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
variable (c : Fin 4 → ℚˣ) (N M : ℕ) {B : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactBoundedCartierEquiv318.Data c N b) (E : ContactBoundedCartierEquiv318.Data c M b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- The actual whole invertible sheaf O(D) tensor O(E)^-1, not merely
a formal subtraction label on parameter points. -/
@[expose] def line : Line (pullback p b) :=
  LineSheafTensor318.line (ContactBoundedCartierAbel318.divisorLine c N b D)
    (FramedLineInverse318.inverse (ContactBoundedCartierAbel318.divisorLine c M b E))
lemma relative_class : OriginalLineAbelTransformation318.point p b (line c N M b D E)=
    OriginalLineAbelTransformation318.point p b (ContactBoundedCartierAbel318.divisorLine c N b D) *
      (OriginalLineAbelTransformation318.point p b (ContactBoundedCartierAbel318.divisorLine c M b E))⁻¹ := by
  change RelativeLineClassQuotient318.classMap (pullback.snd p b)
    (classOf (LineSheafTensor318.line _ (FramedLineInverse318.inverse _)))=_
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse,map_mul,map_inv]
  rfl
lemma value : (RelativeFppfLineSheaf318.unit p).app (op (Over.mk b))
    (OriginalLineAbelTransformation318.point p b (line c N M b D E))=
      (ContactCartierDifferenceAbel318.transformation c).app (op (Over.mk b)) (⟨N,D⟩,⟨M,E⟩) := by
  rw [relative_class,map_mul,map_inv]
  rfl
/-- The difference map commutes with the actual original line pullback
for EVERY test; it is the original Abel transformation of O(D-E). -/
lemma test_value {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)) (f : T ⟶ B) (hf : f ≫ b=t) :
    (OriginalLineAbelTransformation318.transformation p b (line c N M b D E)).app
      (op (Over.mk t)) (Over.homMk f hf)=
    (ContactCartierDifferenceAbel318.transformation c).app (op (Over.mk t))
      ((ContactCartierDifferencePresheaf318.presheaf c).map (Over.homMk f hf).op (⟨N,D⟩,⟨M,E⟩)) := by
  rw [OriginalLineAbelTransformation318.apply,relative_class,map_mul,map_inv,map_mul,map_inv]
  change (ContactBoundedCartierAbel318.transformation c N b D).app (op (Over.mk t)) (Over.homMk f hf) *
    ((ContactBoundedCartierAbel318.transformation c M b E).app (op (Over.mk t)) (Over.homMk f hf))⁻¹=_
  rw [←ContactBoundedCartierAbelNaturality318.test_value,←ContactBoundedCartierAbelNaturality318.test_value]
  rfl
end ContactCartierDifferenceLine318
