module
public import ContactCartierDifferencePresheaf318
public section
noncomputable section
namespace ContactCartierDifferenceAbel318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- Actual divisor difference O(D-E) on the full all-scheme functor,
with values in the original associated fppf line sheaf. -/
@[expose] def transformation : ContactCartierDifferencePresheaf318.presheaf c ⟶
    (RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1} where
  app T D := (ContactCartierAllBoundsPresheaf318.abel c).app T D.1 *
    ((ContactCartierAllBoundsPresheaf318.abel c).app T D.2)⁻¹
  naturality T U f := by
    funext D
    change _=(RelativeFppfLineSheaf318.sheaf p).obj.map f (_ * _⁻¹)
    rw [map_mul,map_inv]
    exact congrArg₂ (fun a b => a*b⁻¹)
      (ContactBoundedCartierAbelNaturality318.natural c D.1.1 _ _
        f.unop.left f.unop.w D.1.2).symm
      (ContactBoundedCartierAbelNaturality318.natural c D.2.1 _ _
        f.unop.left f.unop.w D.2.2).symm
lemma diagonal (T : Over (Spec (CommRingCat.of ℚ)))
    (D : (ContactCartierAllBoundsPresheaf318.presheaf c).obj (op T)) :
    (transformation c).app (op T) (D,D)=1 := mul_inv_cancel _
lemma swapped (T : Over (Spec (CommRingCat.of ℚ)))
    (D : (ContactCartierDifferencePresheaf318.presheaf c).obj (op T)) :
    (transformation c).app (op T) ((ContactCartierDifferencePresheaf318.swap c).app (op T) D)=
      ((transformation c).app (op T) D)⁻¹ := by
  change _ * _⁻¹=(_ * _⁻¹)⁻¹
  simp only [mul_inv_rev,inv_inv]
end ContactCartierDifferenceAbel318
