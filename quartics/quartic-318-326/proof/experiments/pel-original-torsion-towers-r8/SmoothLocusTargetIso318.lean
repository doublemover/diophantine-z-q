module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
namespace SmoothLocusTargetIso318
open AlgebraicGeometry CategoryTheory
variable {X Y Z : Scheme} (f : X ⟶ Y) (e : Y ≅ Z)
  [LocallyOfFinitePresentation f]

/-- Postcomposition by an actual target scheme isomorphism leaves the
whole smooth locus unchanged, including every nonclosed prime. -/
lemma locus : (f ≫ e.hom).smoothLocus=f.smoothLocus := by
  ext x
  rw [Scheme.Hom.mem_smoothLocus,Scheme.Hom.mem_smoothLocus]
  rw [Scheme.Hom.stalkMap_comp,CommRingCat.hom_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (e.hom.stalkMap (f x)) (f.stalkMap x)

/-- An equivariant square with genuine source and target isomorphisms
transports the exact open smooth locus on the source. -/
lemma invariant {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (s : X ≅ X) (t : Y ≅ Y) (h : s.hom ≫ f=f ≫ t.hom) :
    s.hom ⁻¹ᵁ f.smoothLocus=f.smoothLocus := by
  rw [Scheme.Hom.preimage_smoothLocus_eq,h,locus]
end SmoothLocusTargetIso318
