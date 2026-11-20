module
public import SelectedGenericCompactNormalization318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SelectedRationalCompactFromOrdinary318
variable {X Y V V₀ C : Scheme}
  (q : X ⟶ V) (s : Y ⟶ V) (r : V₀ ⟶ V) (e : X ≅ Y)
  (h : e.hom ≫ s = q)
local notation "X₀" => pullback q r
local notation "Y₀" => pullback s r

/-- Actual scalar base change of the already constructed ordinary
comparison. Its projections are the original literal structural maps. -/
@[expose] def ordinaryBaseChange : X₀ ≅ Y₀ := by
  let f := pullback.map q r s r e.hom (𝟙 V₀) (𝟙 V)
    (by simpa only [Category.comp_id] using h.symm)
    (by rw [Category.comp_id,Category.id_comp])
  letI : IsIso f := by dsimp only [f]; infer_instance
  exact asIso f

@[reassoc] theorem ordinaryBaseChange_over :
    (ordinaryBaseChange q s r e h).hom ≫ pullback.snd s r = pullback.snd q r := by
  simp [ordinaryBaseChange]

variable [IsFinite q] [IsIntegral X₀] [IsIntegral C]
  (v : V₀ ⟶ ProjectiveJLine318.scheme ℚ) [IsOpenImmersion v] [QuasiCompact v]
  (i : Y₀ ⟶ C) [IsOpenImmersion i]
  (j : C ⟶ ProjectiveJLine318.scheme ℚ) [IsFinite j]
  (hj : i ≫ j = pullback.snd s r ≫ v)

/-- Complete the SAME rational ordinary-base change by relative
normalization of the literal rational j-line, not by choosing a field
component after extension. -/
@[expose] def compactFromOrdinary
    (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(C,W)) :
    ((pullback.snd q r) ≫ v).normalization ≅ C :=
  SelectedGenericCompactNormalization318.rationalJ (pullback.snd q r) v (pullback.snd s r) i j
    (ordinaryBaseChange q s r e h) (ordinaryBaseChange_over q s r e h) hj normal

theorem compactFromOrdinary_over
    (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(C,W)) :
    (compactFromOrdinary q s r e h v i j hj normal).hom ≫ j =
      ((pullback.snd q r) ≫ v).fromNormalization :=
  SelectedGenericCompactNormalization318.rationalJ_over _ _ _ _ _ _ _ _ _

theorem compactFromOrdinary_open
    (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(C,W)) :
    ((pullback.snd q r) ≫ v).toNormalization ≫ (compactFromOrdinary q s r e h v i j hj normal).hom =
      (ordinaryBaseChange q s r e h).hom ≫ i :=
  SelectedGenericCompactNormalization318.rationalJ_open _ _ _ _ _ _ _ _ _

end SelectedRationalCompactFromOrdinary318

#print axioms SelectedRationalCompactFromOrdinary318.ordinaryBaseChange_over
#print axioms SelectedRationalCompactFromOrdinary318.compactFromOrdinary_over
#print axioms SelectedRationalCompactFromOrdinary318.compactFromOrdinary_open
