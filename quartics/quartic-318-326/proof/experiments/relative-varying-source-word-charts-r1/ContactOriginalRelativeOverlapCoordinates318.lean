module
public import ContactOriginalRelativeOverlap318
public import RelativeOriginalOverlapRingMap318
public section
noncomputable section
namespace ContactOriginalRelativeOverlapCoordinates318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LaurentPolynomial
open ContactOriginalRelativeOverlap318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := LaurentPolynomial ℚ) (A := oldRing c)
    (RingHom.ext_rat _ _)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
local instance : IsScalarTower ℚ (Polynomial ℚ) (ContactOriginalRelativePolynomialCharts318.finiteRing c) :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := Polynomial ℚ) (A := ContactOriginalRelativePolynomialCharts318.finiteRing c)
    (RingHom.ext_rat _ _)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
local instance : IsScalarTower ℚ (Polynomial ℚ) (ContactOriginalRelativePolynomialCharts318.infinityRing c) :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := Polynomial ℚ) (A := ContactOriginalRelativePolynomialCharts318.infinityRing c)
    (RingHom.ext_rat _ _)

/-- Original geometric finite projection, reflected through the fully
faithful ACTUAL Spec functor to the same original ring map. -/
lemma old_finite_square :
    CommRingCat.ofHom (algebraMap (Polynomial ℚ) (ContactOriginalRelativePolynomialCharts318.finiteRing c)) ≫
      CommRingCat.ofHom (finiteMap c).toRingHom =
    CommRingCat.ofHom OriginalLaurentProjectiveOverlap318.finiteHom ≫
      CommRingCat.ofHom (algebraMap (LaurentPolynomial ℚ) (oldRing c)) := by
  apply Spec.map_injective
  rw [Spec.map_comp,Spec.map_comp,rationalMap_spec]
  change oldFiniteEdge c ≫ ContactBicanonicalDegree318.affineMap c =
    Spec.map (CommRingCat.ofHom (algebraMap (LaurentPolynomial ℚ) (oldRing c))) ≫
      OriginalLaurentProjectiveOverlap318.finiteInclusion
  dsimp only [oldFiniteEdge]
  rw [Category.assoc,ContactOriginalLaurentOverlap318.finiteEdge_projection,
    ← Category.assoc,ContactOverlapTensorCharts318.finiteIso_inv_base]

/-- The reciprocal projection is reflected from the very same whole
original overlap scheme, rather than choosing a second Laurent module. -/
lemma old_infinity_square :
    CommRingCat.ofHom (algebraMap (Polynomial ℚ) (ContactOriginalRelativePolynomialCharts318.infinityRing c)) ≫
      CommRingCat.ofHom (infinityMap c).toRingHom =
    CommRingCat.ofHom OriginalLaurentProjectiveOverlap318.infinityHom ≫
      CommRingCat.ofHom (algebraMap (LaurentPolynomial ℚ) (oldRing c)) := by
  apply Spec.map_injective
  rw [Spec.map_comp,Spec.map_comp,rationalMap_spec]
  change oldInfinityEdge c ≫ ContactWholeInfinityScheme318.projection c =
    Spec.map (CommRingCat.ofHom (algebraMap (LaurentPolynomial ℚ) (oldRing c))) ≫
      OriginalLaurentProjectiveOverlap318.infinityInclusion
  dsimp only [oldInfinityEdge]
  rw [Category.assoc,ContactOriginalLaurentOverlap318.infinityEdge_projection,
    ← Category.assoc,ContactOverlapTensorCharts318.finiteIso_inv_base]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma old_finite_coordinate :
    finiteMap c (algebraMap (Polynomial ℚ) (ContactOriginalRelativePolynomialCharts318.finiteRing c) Polynomial.X) =
      algebraMap (LaurentPolynomial ℚ) (oldRing c) (T 1) := by
  have h := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (old_finite_square c)) Polynomial.X
  simpa only [CommRingCat.hom_comp,RingHom.comp_apply,CommRingCat.hom_ofHom,
    OriginalLaurentProjectiveOverlap318.finiteHom,Polynomial.toLaurent_X] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma old_infinity_coordinate :
    infinityMap c (algebraMap (Polynomial ℚ) (ContactOriginalRelativePolynomialCharts318.infinityRing c) Polynomial.X) =
      algebraMap (LaurentPolynomial ℚ) (oldRing c) (T (-1)) := by
  have h := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (old_infinity_square c)) Polynomial.X
  simpa only [CommRingCat.hom_comp,RingHom.comp_apply,CommRingCat.hom_ofHom,
    OriginalLaurentProjectiveOverlap318.infinityHom_X] using h

/-- The unchanged original common overlap ring with its proved Laurent R
coordinate action, including the actual coefficient action. -/
abbrev laurentMap := RelativeOriginalLaurentAlgebra318.laurentMap ℚ R (oldRing c)

lemma finite_square :
    (RelativeOriginalAffineChartMap318.ringMap (CommRingCat.of ℚ) R
      (ContactOriginalRelativePolynomialCharts318.finiteRing c) (oldRing c) (finiteMap c)).hom.comp
        (RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R
          (ContactOriginalRelativePolynomialCharts318.finiteRing c)) =
      (laurentMap R c).comp Polynomial.toLaurent :=
  RelativeOriginalOverlapRingMap318.finite_square ℚ R
    (ContactOriginalRelativePolynomialCharts318.finiteRing c) (oldRing c)
    (finiteMap c) (old_finite_coordinate c)

lemma infinity_square :
    (RelativeOriginalAffineChartMap318.ringMap (CommRingCat.of ℚ) R
      (ContactOriginalRelativePolynomialCharts318.infinityRing c) (oldRing c) (infinityMap c)).hom.comp
        (RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R
          (ContactOriginalRelativePolynomialCharts318.infinityRing c)) =
      (laurentMap R c).comp (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) :=
  RelativeOriginalOverlapRingMap318.infinity_square ℚ R
    (ContactOriginalRelativePolynomialCharts318.infinityRing c) (oldRing c)
    (infinityMap c) (old_infinity_coordinate c)
end ContactOriginalRelativeOverlapCoordinates318
