module
public import LineSheafClassGroup318
public import CompletedCharacterLineClassNorm318
public import CompletedCharacterNormUnit318
public import CompletedCharacterNormTensor318
public section
noncomputable section
namespace CompletedCharacterLineNormHom318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open CompletedCharacterGlobal318 CompletedCharacterSchemeMaps318 CompletedCharacterNormLine318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma norm_unit (i : Fin 4) : CompletedCharacterLineClassNorm318.norm i 1 = 1 := by
  change classOf (CompletedCharacterNormLine318.line i (LineSheafUnit318.line Model)) =
    classOf (LineSheafUnit318.line (Target i))
  exact classOf_eq (CompletedCharacterNormUnit318.lineIso i (LineSheafUnit318.line Model) (Iso.refl _))
lemma norm_product (i : Fin 4) (c d : Class Model) :
    CompletedCharacterLineClassNorm318.norm i (c * d) =
      CompletedCharacterLineClassNorm318.norm i c * CompletedCharacterLineClassNorm318.norm i d := by
  induction c, d using Quotient.inductionOn₂ with
  | h L N => exact classOf_eq (CompletedCharacterNormTensor318.lineIso i L N)
/-- Each original completed character norm is a homomorphism of the genuine
original line-sheaf isomorphism-class groups. -/
@[expose] def norm (i : Fin 4) : Class Model →* Class (Target i) where
  toFun := CompletedCharacterLineClassNorm318.norm i
  map_one' := norm_unit i
  map_mul' := norm_product i
lemma apply_eq (i : Fin 4) (c : Class Model) :
    norm i c = CompletedCharacterLineClassNorm318.norm i c := rfl
lemma on_representatives (i : Fin 4) (L : Line Model) :
    norm i (classOf L) = classOf (CompletedCharacterNormLine318.line i L) := rfl
lemma maps_inverse (i : Fin 4) (c : Class Model) :
    norm i (c⁻¹) = (norm i c)⁻¹ := map_inv (norm i) c
lemma maps_power (i : Fin 4) (c : Class Model) (n : ℕ) :
    norm i (c ^ n) = norm i c ^ n := map_pow (norm i) c n
end CompletedCharacterLineNormHom318
