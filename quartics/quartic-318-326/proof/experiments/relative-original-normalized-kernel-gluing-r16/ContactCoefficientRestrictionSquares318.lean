module
public import ContactCoefficientSectionEquivalences318
public import OriginalLineSquareSections318
public import OriginalAffinePathWholeSections318
public section
noncomputable section
namespace ContactCoefficientRestrictionSquares318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactRelativeCoefficientChange318
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))

/-- The first actual section square: the genuine finite-chart
restriction and original coefficient pullback commute on all sections. -/
lemma finite (m : finiteSections R c L) :
    ContactCoefficientLineCharts318.overlapRestriction R S f c L
      (ContactOriginalRelativeLineOverlap318.finiteRestriction R c L m) =
    ContactOriginalRelativeLineOverlap318.finiteRestriction S c
      (ContactCoefficientLineCharts318.pulledLine R S f c L)
        (ContactCoefficientLineCharts318.finiteRestriction R S f c L m) := by
  have h := OriginalLineSquareSections318.original_square
    (curveMap R S f c) (finiteInto R c) (into R c) (finiteEdge R c)
    (finiteEdge_into R c) (finiteInto S c) (into S c) (finiteEdge S c)
    (finiteEdge_into S c) (Spec.map (finiteRingMap R S f c))
    (Spec.map (overlapRingMap R S f c)) (finite_square R S f c)
    (overlap_square R S f c) (finite_edge_square R S f c) L.object m
  simpa only [ContactCoefficientLineCharts318.overlapRestriction,
    ContactCoefficientLineCharts318.finiteRestriction,ContactCoefficientLineCharts318.pulledLine,
    OriginalCoefficientChartLine318.originalRestriction,
    ContactOriginalRelativeLineOverlap318.finiteRestriction,
    OriginalAffinePathWholeSections318.restriction_direct,
    ContactOriginalRelativeLineOverlap318.finiteComparison,
    ContactOriginalRelativeLineOverlap318.finiteArrow,
    ContactOriginalRelativeLineOverlap318.finiteLine,
    ContactOriginalRelativeOverlap318.finiteEdge,
    OriginalLineAffineModel318.sections,LineSheafPullback318.line,
    OriginalCoefficientChartLine318.sheafComparison,OriginalPullbackSquarePasting318.comparison,
    OriginalOpenPullbackSections318.sectionPull,OriginalSectionPullbackComposition318.pull,
    PullbackPathComposition318.iso,Iso.trans_hom,Iso.symm_hom,
    Iso.trans_inv,Iso.refl_hom,Iso.refl_inv,NatTrans.comp_app,
    Iso.app_hom,Iso.app_inv,Scheme.Modules.pullbackCongr,eqToIso_refl,
    NatTrans.id_app,Category.comp_id,Category.id_comp,Category.assoc] using h

/-- The second square is proved on the DISTINCT infinity chart with its
actual reciprocal restriction, ending in the SAME full overlap. -/
lemma infinity (m : infinitySections R c L) :
    ContactCoefficientLineCharts318.overlapRestriction R S f c L
      (ContactOriginalRelativeLineOverlap318.infinityRestriction R c L m) =
    ContactOriginalRelativeLineOverlap318.infinityRestriction S c
      (ContactCoefficientLineCharts318.pulledLine R S f c L)
        (ContactCoefficientLineCharts318.infinityRestriction R S f c L m) := by
  have h := OriginalLineSquareSections318.original_square
    (curveMap R S f c) (infinityInto R c) (into R c) (infinityEdge R c)
    (infinityEdge_into R c) (infinityInto S c) (into S c) (infinityEdge S c)
    (infinityEdge_into S c) (Spec.map (infinityRingMap R S f c))
    (Spec.map (overlapRingMap R S f c)) (infinity_square R S f c)
    (overlap_square R S f c) (infinity_edge_square R S f c) L.object m
  simpa only [ContactCoefficientLineCharts318.overlapRestriction,
    ContactCoefficientLineCharts318.infinityRestriction,ContactCoefficientLineCharts318.pulledLine,
    OriginalCoefficientChartLine318.originalRestriction,
    ContactOriginalRelativeLineOverlap318.infinityRestriction,
    OriginalAffinePathWholeSections318.restriction_direct,
    ContactOriginalRelativeLineOverlap318.infinityComparison,
    ContactOriginalRelativeLineOverlap318.infinityArrow,
    ContactOriginalRelativeLineOverlap318.infinityLine,
    ContactOriginalRelativeOverlap318.infinityEdge,
    OriginalLineAffineModel318.sections,LineSheafPullback318.line,
    OriginalCoefficientChartLine318.sheafComparison,OriginalPullbackSquarePasting318.comparison,
    OriginalOpenPullbackSections318.sectionPull,OriginalSectionPullbackComposition318.pull,
    PullbackPathComposition318.iso,Iso.trans_hom,Iso.symm_hom,
    Iso.trans_inv,Iso.refl_hom,Iso.refl_inv,NatTrans.comp_app,
    Iso.app_hom,Iso.app_inv,Scheme.Modules.pullbackCongr,eqToIso_refl,
    NatTrans.id_app,Category.comp_id,Category.id_comp,Category.assoc] using h
end ContactCoefficientRestrictionSquares318
