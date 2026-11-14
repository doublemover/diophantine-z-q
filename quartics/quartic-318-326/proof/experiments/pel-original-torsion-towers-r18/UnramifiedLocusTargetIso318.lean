module
public import SchemeUnramifiedLocus318
public section
noncomputable section
namespace UnramifiedLocusTargetIso318
open AlgebraicGeometry CategoryTheory SchemeUnramifiedLocus318
variable {X Y Z : Scheme} (f : X ⟶ Y) (e : Y ≅ Z)
  [LocallyOfFinitePresentation f]

/-- Postcomposition by an actual target scheme isomorphism leaves the
whole unramified locus unchanged, including every nonclosed prime. -/
lemma target : locus (f ≫ e.hom)=locus f := by
  ext x
  rw [mem_locus,mem_locus]
  rw [Scheme.Hom.stalkMap_comp,CommRingCat.hom_comp]
  exact RingHom.FormallyUnramified.respectsIso.cancel_left_isIso
    (e.hom.stalkMap (f x)) (f.stalkMap x)

/-- An equivariant square with genuine source and target isomorphisms
transports the exact open unramified locus on the source. -/
lemma invariant {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (s : X ≅ X) (t : Y ≅ Y) (h : s.hom ≫ f=f ≫ t.hom) :
    s.hom ⁻¹ᵁ locus f=locus f := by
  rw [preimage_locus_eq,h,target]
end UnramifiedLocusTargetIso318
