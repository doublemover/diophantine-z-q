module
public import OriginalRelativeOpenBaseChange318
public section
noncomputable section
namespace ContactRelativeFppfSeparated318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalRelativeSite318 OriginalRelativeOpenBaseChange318 ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {X Y : Scheme} (b : Y ⟶ FieldBase t) (b' : X ⟶ FieldBase t)
  (f : X ⟶ Y) (hf : f ≫ b = b') [Flat f] [Surjective f] [LocallyOfFinitePresentation f]

/-- Actual fppf pullback detects original relative classes on every
original test base, using all affine opens and genuine open base changes. -/
lemma injective : Function.Injective ((presheaf (q t)).map (arrow b b' f hf).op) := by
  intro c d hcd
  apply (ContactRelativeOpenPresieve318.isSheafFor t b (fun U : Y.affineOpens => U.1)
    (affine_cover (Y:=Y))).isSeparatedFor.ext
  rintro Z a ⟨U⟩
  letI : IsAffine U.1.toScheme := U.2
  letI : Flat (f ∣_ U.1) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f U.1).flip (inferInstance : Flat f)
  letI : Surjective (f ∣_ U.1) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f U.1).flip (inferInstance : Surjective f)
  letI : LocallyOfFinitePresentation (f ∣_ U.1) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f U.1).flip (inferInstance : LocallyOfFinitePresentation f)
  have hi := (Presieve.isSeparatedFor_singleton (presheaf (q t))).mp
    (ContactRelativeAffinePresieve318.isSheafFor t (U.1.ι ≫ b) ((f ⁻¹ᵁ U.1).ι ≫ b')
      (f ∣_ U.1) (base_square b b' f hf U.1)).isSeparatedFor
  apply hi
  have hh := congrArg ((presheaf (q t)).map (openArrow b' (f ⁻¹ᵁ U.1)).op) hcd
  simpa only [← Functor.map_comp_apply,← op_comp,square] using hh
end ContactRelativeFppfSeparated318
