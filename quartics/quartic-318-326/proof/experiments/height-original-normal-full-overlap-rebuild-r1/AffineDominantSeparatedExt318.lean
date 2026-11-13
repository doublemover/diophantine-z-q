module
public import AffineFractionGeneric318
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public section
noncomputable section
namespace AffineDominantSeparatedExt318
open AlgebraicGeometry CategoryTheory
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- The literal injection supplies scheme-theoretic density; no rational
point or cardinality comparison is substituted. -/
lemma dominant (f : A →+* B) (hf : Function.Injective f) :
    IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap f)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
  exact bot_le

/-- Agreement on a dominant source suffices over a separated affine base.
The equality of the base maps is proved first, not assumed by type. -/
lemma ext_over_affine {W X Y : Scheme.{u}} [IsReduced X]
    (R : CommRingCat.{u}) (s : Y ⟶ Spec R) [IsSeparated s]
    (ι : W ⟶ X) [IsDominant ι] {f g : X ⟶ Y}
    (h : ι ≫ f=ι ≫ g) : f=g := by
  have hb : f ≫ s=g ≫ s :=
    AlgebraicGeometry.ext_of_isDominant ι
      (by simpa only [Category.assoc] using congrArg (fun k => k ≫ s) h)
  exact ext_of_isDominant_of_isSeparated s hb ι h
end AffineDominantSeparatedExt318
