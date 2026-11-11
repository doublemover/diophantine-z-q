module
public import ClutchedTensorIsomorphism318
public import NormalizedWholeBicanonicalSheaf318
public section
noncomputable section
namespace NormalizedWholeIntrinsicTensor318
open AlgebraicGeometry CategoryTheory
open NormalizedWholeGluing318 NormalizedWholeOpenMaps318
open NormalizedWholeDualitySheaf318
universe u
variable (R : Type u) [CommRing R] (d a : Fin 4 → R)
local notation "L" => NormalizedWholeDualitySheaf318.line R d a
local notation "B" => NormalizedWholeBicanonicalSheaf318.line R d a

/-- The actual sheafified tensor square of the ORIGINAL global whole-model
line, identified with its already constructed squared-transition module.
Both maps are genuine categorical inverses on the entire model. -/
@[expose] def iso : IntrinsicTensorSheaf318.tensor L L ≅ B :=
  ClutchedTensorIsomorphism318.isoTo
    (finiteChart R d a) (infinityChart R d a) (intoFinite R d a) (intoInfinity R d a)
    (gluing_square R d a) (sectionUnit R d a).val (sectionUnit R d a).val
    (sectionUnit R d a).isUnit (sectionUnit R d a).isUnit
    (finite_range R d a) (infinity_range R d a) (cover_top R d a)
    (NormalizedWholeBicanonicalSheaf318.sectionUnit R d a).val
    (by simpa only [pow_two] using NormalizedWholeBicanonicalSheaf318.transition_square R d a)

lemma hom_inv : (iso R d a).hom ≫ (iso R d a).inv = 𝟙 _ := (iso R d a).hom_inv_id
lemma inv_hom : (iso R d a).inv ≫ (iso R d a).hom = 𝟙 _ := (iso R d a).inv_hom_id

/-- The whole finite-chart coefficient of a pure tensor is literally the
product of the two original coefficients. -/
lemma finite_pure (V : (scheme R d a).Opens) (m n : Γ(L,V)) :
    (ClutchedModule318.first (finiteChart R d a) (infinityChart R d a)
      (intoFinite R d a) (intoInfinity R d a) (gluing_square R d a)
      (NormalizedWholeBicanonicalSheaf318.sectionUnit R d a).val).app V
      ((iso R d a).hom.app V (IntrinsicTensorSheaf318.pure L L V m n)) =
    (ClutchedModule318.first (finiteChart R d a) (infinityChart R d a)
      (intoFinite R d a) (intoInfinity R d a) (gluing_square R d a) (sectionUnit R d a).val).app V m *
    (ClutchedModule318.first (finiteChart R d a) (infinityChart R d a)
      (intoFinite R d a) (intoInfinity R d a) (gluing_square R d a) (sectionUnit R d a).val).app V n := by
  have he := ClutchedTensorIsomorphism318.isoTo_first
    (finiteChart R d a) (infinityChart R d a) (intoFinite R d a) (intoInfinity R d a)
    (gluing_square R d a) (sectionUnit R d a).val (sectionUnit R d a).val
    (sectionUnit R d a).isUnit (sectionUnit R d a).isUnit
    (finite_range R d a) (infinity_range R d a) (cover_top R d a)
    (NormalizedWholeBicanonicalSheaf318.sectionUnit R d a).val
    (by simpa only [pow_two] using NormalizedWholeBicanonicalSheaf318.transition_square R d a)
  exact (congrArg (fun f => f.app V (IntrinsicTensorSheaf318.pure L L V m n)) he).trans
    (ClutchedTensorMultiplication318.first_pure _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- Both specified global sections now live in the GENUINE intrinsic tensor
square; their images are the unchanged global model sections, not replacements. -/
@[expose] def section0 : Γ(IntrinsicTensorSheaf318.tensor L L,⊤) :=
  (iso R d a).inv.app ⊤ (NormalizedWholeBicanonicalSheaf318.section0 R d a)
@[expose] def section1 : Γ(IntrinsicTensorSheaf318.tensor L L,⊤) :=
  (iso R d a).inv.app ⊤ (NormalizedWholeBicanonicalSheaf318.section1 R d a)
lemma section0_image : (iso R d a).hom.app ⊤ (section0 R d a) =
    NormalizedWholeBicanonicalSheaf318.section0 R d a := by
  exact congrArg (fun f => f.app ⊤ (NormalizedWholeBicanonicalSheaf318.section0 R d a))
    (iso R d a).inv_hom_id
lemma section1_image : (iso R d a).hom.app ⊤ (section1 R d a) =
    NormalizedWholeBicanonicalSheaf318.section1 R d a := by
  exact congrArg (fun f => f.app ⊤ (NormalizedWholeBicanonicalSheaf318.section1 R d a))
    (iso R d a).inv_hom_id
end NormalizedWholeIntrinsicTensor318
