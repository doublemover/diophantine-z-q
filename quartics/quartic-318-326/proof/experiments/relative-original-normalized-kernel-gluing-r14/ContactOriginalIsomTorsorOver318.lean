module
public import ContactOriginalIsomShearInverse318
public section
noncomputable section
namespace ContactOriginalIsomTorsorOver318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
open ContactIsomParameterProduct318 ContactOriginalIsomShearMaps318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
/-- The ACTUAL principal-action comparison: Aut(L) times Isom(L,K) is
isomorphic to Isom(L,K) times Isom(L,K), over the original coefficient base.
This is a scheme isomorphism, with no choice of an Isom point. -/
@[expose] def schemeIso : source R c L K ≅ target R c L K where
  hom := shear R c L K
  inv := unshear R c L K
  hom_inv_id := ContactOriginalIsomShearInverse318.hom_inv R c L K
  inv_hom_id := ContactOriginalIsomShearInverse318.inv_hom R c L K
lemma shear_over : shear R c L K ≫ base R c L K L K=base R c L L L K := by
  change shear R c L K ≫ (pullback.fst _ _ ≫ _)=_
  rw [←Category.assoc,shear_fst]
  exact ContactOriginalIsomGeometricComposition318.composition_over R c L L K
lemma unshear_over : unshear R c L K ≫ base R c L L L K=base R c L K L K := by
  change unshear R c L K ≫ (pullback.fst _ _ ≫ _)=_
  rw [←Category.assoc,unshear_fst]
  exact difference_base R c L K
/-- Exact over-base version of the same geometric isomorphism. The
stabilizer is the FULL original automorphism parameter, not assumed Gm. -/
@[expose] def overIso : Over.mk (base R c L L L K) ≅ Over.mk (base R c L K L K) where
  hom := Over.homMk (shear R c L K) (shear_over R c L K)
  inv := Over.homMk (unshear R c L K) (unshear_over R c L K)
  hom_inv_id := by
    apply Over.OverMorphism.ext
    exact ContactOriginalIsomShearInverse318.hom_inv R c L K
  inv_hom_id := by
    apply Over.OverMorphism.ext
    exact ContactOriginalIsomShearInverse318.inv_hom R c L K
end ContactOriginalIsomTorsorOver318
