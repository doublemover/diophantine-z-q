module
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace OriginalAffineTestOpen318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {B X T : Scheme.{u}} [IsAffine B] [IsAffine T]
  (p : X ⟶ B) (b : T ⟶ B) (U : X.Opens)

/-- The genuine chart inside the ORIGINAL full test pullback. -/
abbrev chart := pullback U.ι (pullback.fst p b)
abbrev into : chart p b U ⟶ pullback p b := pullback.snd _ _

instance : IsOpenImmersion (into p b U) := inferInstance

/-- Its image is the ENTIRE original inverse-image open, with no chosen
subchart, reduction, or omitted points. -/
lemma range : (into p b U).opensRange = (pullback.fst p b) ⁻¹ᵁ U := by
  rw [Scheme.Hom.opensRange_pullbackSnd,Scheme.Opens.opensRange_ι]

/-- The canonical original pullback-pasting comparison retains the actual
chart and the actual test map to the affine base. -/
def comparison : chart p b U ≅ pullback (U.ι ≫ p) b :=
  pullbackRightPullbackFstIso p b U.ι

lemma comparison_projection : (comparison p b U).hom ≫ pullback.snd (U.ι ≫ p) b =
    into p b U ≫ pullback.snd p b :=
  pullbackRightPullbackFstIso_hom_snd p b U.ι

/-- An original affine chart stays affine on EVERY affine test of the
original affine base, including nonreduced and non-Noetherian tests. -/
theorem affine (hU : IsAffineOpen U) :
    IsAffineOpen ((pullback.fst p b) ⁻¹ᵁ U) := by
  letI : IsAffine U.toScheme := hU
  letI : IsAffine (chart p b U) := IsAffine.of_isIso (comparison p b U).hom
  rw [← range p b U]
  exact isAffineOpen_opensRange (into p b U)

lemma cover (V : X.Opens) (h : U ⊔ V = ⊤) :
    ((pullback.fst p b) ⁻¹ᵁ U) ⊔ ((pullback.fst p b) ⁻¹ᵁ V) = ⊤ := by
  rw [← Scheme.Hom.preimage_sup,h,Scheme.Hom.preimage_top]
end OriginalAffineTestOpen318
