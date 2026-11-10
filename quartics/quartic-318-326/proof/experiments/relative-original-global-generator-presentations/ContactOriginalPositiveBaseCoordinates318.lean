module
public import OriginalOpenRingRestrictionPath318
public import ContactOriginalTwistPower318
public section
noncomputable section
namespace ContactOriginalPositiveBaseCoordinates318
open AlgebraicGeometry CategoryTheory Opposite Polynomial
open ContactOriginalWholeRestriction318 ContactOriginalLaurentOverlap318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
abbrev X := ContactProjectiveModel318.model c

/-- Original polynomial coordinate on the entire original finite chart. -/
def finiteCoordinate : Γ(X c,finiteOpen c) :=
  ((SourceGlobalAffine318.chartEmbedding c).appIso ⊤).inv
    ((ContactBicanonicalDegree318.affineMap c).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv Polynomial.X))

/-- Original reciprocal polynomial coordinate on the entire infinity chart. -/
def infinityCoordinate : Γ(X c,infinityOpen c) :=
  ((ContactWholeInfinityScheme318.into c).appIso ⊤).inv
    ((ContactWholeInfinityScheme318.projection c).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv Polynomial.X))

lemma finite_restriction : (X c).presheaf.map (homOfLE inf_le_left).op (finiteCoordinate c) =
    ContactOriginalTwistingLine318.scalar c (LaurentPolynomial.T 1) := by
  have hp := OriginalOpenRingRestrictionPath318.apply (finiteEdge c)
    (SourceGlobalAffine318.chartEmbedding c) (into c) (finiteEdge_into c)
    (finiteOpen c ⊓ infinityOpen c) (overlap_image c)
    ((ContactBicanonicalDegree318.affineMap c).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv Polynomial.X))
  have hb := congrArg (fun q => q.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv Polynomial.X))
    (finiteEdge_projection c)
  simp only [Scheme.Hom.comp_appTop,ConcreteCategory.comp_apply] at hb
  rw [hb] at hp
  have hn := (congrArg (fun q => q Polynomial.X)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom OriginalLaurentProjectiveOverlap318.finiteHom))).symm
  change (OriginalLaurentProjectiveOverlap318.finiteInclusion).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv Polynomial.X) =
      (Scheme.ΓSpecIso (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)).inv
        (OriginalLaurentProjectiveOverlap318.finiteHom Polynomial.X) at hn
  rw [hn] at hp
  simpa only [finiteCoordinate,OriginalLaurentProjectiveOverlap318.finiteHom,Polynomial.toLaurent_X] using hp

lemma infinity_restriction : (X c).presheaf.map (homOfLE inf_le_right).op (infinityCoordinate c) =
    ContactOriginalTwistingLine318.scalar c (LaurentPolynomial.T (-1)) := by
  have hp := OriginalOpenRingRestrictionPath318.apply (infinityEdge c)
    (ContactWholeInfinityScheme318.into c) (into c) (infinityEdge_into c)
    (finiteOpen c ⊓ infinityOpen c) (overlap_image c)
    ((ContactWholeInfinityScheme318.projection c).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv Polynomial.X))
  have hb := congrArg (fun q => q.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv Polynomial.X))
    (infinityEdge_projection c)
  simp only [Scheme.Hom.comp_appTop,ConcreteCategory.comp_apply] at hb
  rw [hb] at hp
  have hn := (congrArg (fun q => q Polynomial.X)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom OriginalLaurentProjectiveOverlap318.infinityHom))).symm
  change (OriginalLaurentProjectiveOverlap318.infinityInclusion).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv Polynomial.X) =
      (Scheme.ΓSpecIso (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)).inv
        (OriginalLaurentProjectiveOverlap318.infinityHom Polynomial.X) at hn
  rw [hn,OriginalLaurentProjectiveOverlap318.infinityHom_X] at hp
  exact hp
end ContactOriginalPositiveBaseCoordinates318
