module
public import ContactOriginalRelativeOverlapCoordinates318
public import OriginalAffineLinePathSections318
public import PullbackPathComposition318
public section
noncomputable section
namespace ContactOriginalRelativeLineOverlap318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativeOverlap318 ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))

/-- The SAME original global line on the ONE actual entire overlap. -/
abbrev line := LineSheafPullback318.line (into R c) L
abbrev finiteLine := LineSheafPullback318.line (finiteInto R c) L
abbrev infinityLine := LineSheafPullback318.line (infinityInto R c) L

@[expose] def finiteComparison : (Scheme.Modules.pullback (finiteEdge R c)).obj (finiteLine R c L).object ≅
    (line R c L).object :=
  (PullbackPathComposition318.iso (finiteEdge R c) (finiteInto R c)
    (into R c) (finiteEdge_into R c)).app L.object

@[expose] def infinityComparison : (Scheme.Modules.pullback (infinityEdge R c)).obj (infinityLine R c L).object ≅
    (line R c L).object :=
  (PullbackPathComposition318.iso (infinityEdge R c) (infinityInto R c)
    (into R c) (infinityEdge_into R c)).app L.object

def transition : (Scheme.Modules.pullback (infinityEdge R c)).obj (infinityLine R c L).object ≅
    (Scheme.Modules.pullback (finiteEdge R c)).obj (finiteLine R c L).object :=
  infinityComparison R c L ≪≫ (finiteComparison R c L).symm

@[reassoc] lemma transition_recovery : (transition R c L).hom ≫ (finiteComparison R c L).hom =
    (infinityComparison R c L).hom := by
  simp only [transition,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]

abbrev finiteArrow := RelativeOriginalAffineChartMap318.ringMap (CommRingCat.of ℚ) R
  (finiteRing c) (oldRing c) (finiteMap c)
abbrev infinityArrow := RelativeOriginalAffineChartMap318.ringMap (CommRingCat.of ℚ) R
  (infinityRing c) (oldRing c) (infinityMap c)
abbrev originalSections := OriginalLineAffineModel318.sections (ring R c) (line R c L)

/-- Both genuine original geometric restrictions end in the SAME original
section module, before any Laurent scalar restriction or cohomology quotient. -/
abbrev finiteRestriction := OriginalAffineLinePathSections318.restriction (finiteArrow R c)
  (finiteLine R c L) (line R c L) (finiteComparison R c L)
abbrev infinityRestriction := OriginalAffineLinePathSections318.restriction (infinityArrow R c)
  (infinityLine R c L) (line R c L) (infinityComparison R c L)

lemma finite_unit (m : finiteSections R c L) :
    (OriginalAffineLinePathSections318.comparison (finiteArrow R c)
      (finiteLine R c L) (line R c L) (finiteComparison R c L)).hom
        ((ModuleCat.extendRestrictScalarsAdj (finiteArrow R c).hom).unit.app _ m) =
      finiteRestriction R c L m :=
  OriginalAffineLinePathSections318.unit_apply _ _ _ _ m

lemma infinity_unit (m : infinitySections R c L) :
    (OriginalAffineLinePathSections318.comparison (infinityArrow R c)
      (infinityLine R c L) (line R c L) (infinityComparison R c L)).hom
        ((ModuleCat.extendRestrictScalarsAdj (infinityArrow R c).hom).unit.app _ m) =
      infinityRestriction R c L m :=
  OriginalAffineLinePathSections318.unit_apply _ _ _ _ m

lemma finite_polynomial (p : Polynomial R) (m : finiteSections R c L) :
    finiteRestriction R c L (p • m) =
      ContactOriginalRelativeOverlapCoordinates318.laurentMap R c (Polynomial.toLaurent p) •
        finiteRestriction R c L m := by
  change finiteRestriction R c L
    (RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R (finiteRing c) p • m) = _
  rw [OriginalAffineLinePathSections318.restriction_smul]
  exact congrArg (fun a => a • finiteRestriction R c L m)
    (RingHom.congr_fun (ContactOriginalRelativeOverlapCoordinates318.finite_square R c) p)

lemma infinity_polynomial (p : Polynomial R) (m : infinitySections R c L) :
    infinityRestriction R c L (p • m) =
      ContactOriginalRelativeOverlapCoordinates318.laurentMap R c
        (LaurentPolynomial.invert (Polynomial.toLaurent p)) • infinityRestriction R c L m := by
  change infinityRestriction R c L
    (RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R (infinityRing c) p • m) = _
  rw [OriginalAffineLinePathSections318.restriction_smul]
  exact congrArg (fun a => a • infinityRestriction R c L m)
    (RingHom.congr_fun (ContactOriginalRelativeOverlapCoordinates318.infinity_square R c) p)
end ContactOriginalRelativeLineOverlap318
