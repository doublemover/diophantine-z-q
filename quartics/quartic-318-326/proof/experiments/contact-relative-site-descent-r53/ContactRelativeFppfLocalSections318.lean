module
public import PresheafSingletonSquares318
public section
noncomputable section
namespace ContactRelativeFppfLocalSections318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalRelativeSite318 OriginalRelativeOpenBaseChange318 ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {X Y : Scheme} (b : Y ⟶ FieldBase t) (b' : X ⟶ FieldBase t)
  (f : X ⟶ Y) (hf : f ≫ b = b') [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
  (x : (presheaf (q t)).obj (op (object b')))
  (hx : ∀ {Z : Over (FieldBase t)} (u v : Z ⟶ object b'),
    u ≫ arrow b b' f hf = v ≫ arrow b b' f hf →
      (presheaf (q t)).map u.op x = (presheaf (q t)).map v.op x)

include hx in
lemma exists_local (U : Y.affineOpens) : ∃! y,
    (presheaf (q t)).map (restrictedArrow b b' f hf U.1).op y =
      (presheaf (q t)).map (openArrow b' (f ⁻¹ᵁ U.1)).op x := by
  letI : IsAffine U.1.toScheme := U.2
  letI : Flat (f ∣_ U.1) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f U.1).flip (inferInstance : Flat f)
  letI : Surjective (f ∣_ U.1) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f U.1).flip (inferInstance : Surjective f)
  letI : LocallyOfFinitePresentation (f ∣_ U.1) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f U.1).flip (inferInstance : LocallyOfFinitePresentation f)
  apply (Presieve.isSheafFor_singleton (presheaf (q t))).mp
    (ContactRelativeAffinePresieve318.isSheafFor t (U.1.ι ≫ b) ((f ⁻¹ᵁ U.1).ι ≫ b')
      (f ∣_ U.1) (base_square b b' f hf U.1))
  exact PresheafSingletonSquares318.compatible (presheaf (q t)) (arrow b b' f hf)
    (restrictedArrow b b' f hf U.1) (openArrow b U.1) (openArrow b' (f ⁻¹ᵁ U.1))
    (square b b' f hf U.1) x hx

@[expose] def localSection (U : Y.affineOpens) : (presheaf (q t)).obj (op (openObject b U.1)) :=
  (exists_local t b b' f hf x hx U).exists.choose

lemma localSection_recovery (U : Y.affineOpens) :
    (presheaf (q t)).map (restrictedArrow b b' f hf U.1).op (localSection t b b' f hf x hx U) =
      (presheaf (q t)).map (openArrow b' (f ⁻¹ᵁ U.1)).op x :=
  (exists_local t b b' f hf x hx U).exists.choose_spec

/-- The exact local solution has the required recovery on every smaller
base open, including non-affine intersections. -/
lemma local_restrict (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) :
    (presheaf (q t)).map (restrictedArrow b b' f hf V).op
      ((presheaf (q t)).map (openInclusion b h).op (localSection t b b' f hf x hx U)) =
        (presheaf (q t)).map (openArrow b' (f ⁻¹ᵁ V)).op x := by
  rw [PresheafSingletonSquares318.map_square (presheaf (q t))
    (restrictedArrow b b' f hf U.1) (restrictedArrow b b' f hf V)
    (openInclusion b h) (openInclusion b' (f.preimage_mono h)) (nested b b' f hf h),
    localSection_recovery,← Functor.map_comp_apply,← op_comp,openInclusion_arrow]

lemma matching (U V : Y.affineOpens) :
    (presheaf (q t)).map (openInclusion b (show U.1 ⊓ V.1 ≤ U.1 from inf_le_left)).op
        (localSection t b b' f hf x hx U) =
      (presheaf (q t)).map (openInclusion b (show U.1 ⊓ V.1 ≤ V.1 from inf_le_right)).op
        (localSection t b b' f hf x hx V) := by
  let W := U.1 ⊓ V.1
  letI : Flat (f ∣_ W) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f W).flip (inferInstance : Flat f)
  letI : Surjective (f ∣_ W) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f W).flip (inferInstance : Surjective f)
  letI : LocallyOfFinitePresentation (f ∣_ W) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f W).flip (inferInstance : LocallyOfFinitePresentation f)
  apply ContactRelativeFppfSeparated318.injective t (W.ι ≫ b) ((f ⁻¹ᵁ W).ι ≫ b')
    (f ∣_ W) (base_square b b' f hf W)
  exact (local_restrict t b b' f hf x hx U W inf_le_left).trans
    (local_restrict t b b' f hf x hx V W inf_le_right).symm
end ContactRelativeFppfLocalSections318
