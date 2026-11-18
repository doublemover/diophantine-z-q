module
public import OriginalPrimeThreeNonregularPoint318
public import OriginalIntegerClosureGluing318
public section
noncomputable section
namespace OriginalPrimeThreeNonregularSchemePoint318
open AlgebraicGeometry CategoryTheory
open OriginalPrimeThreeFirstOrderPoint318
open OriginalPrimeThreeCotangentIndependence318
open OriginalPrimeThreeLocalizedCotangent318
open OriginalPrimeThreeNonregularPoint318

abbrev Model := OriginalIntegerClosureGluing318.model OriginalPrimeThreeActualQuotient318.twist

/-- The explicit maximal ideal is an actual point of the finite chart. -/
@[expose] def finitePoint : Spec (CommRingCat.of Closure) :=
  ⟨pointIdeal, inferInstance⟩

/-- Its image lies in the actual glued normalization by the constructed
open chart, not by an assumed comparison with another model. -/
@[expose] def actualSchemePoint : Model :=
  OriginalIntegerClosureGluing318.finiteChart OriginalPrimeThreeActualQuotient318.twist finitePoint

/-- Nonregularity transports to the actual scheme stalk along the native
affine stalk isomorphism and the actual finite-chart open immersion. -/
theorem actual_normalized_scheme_point_not_regular :
    ¬ IsRegularLocalRing (Model.presheaf.stalk actualSchemePoint) := by
  intro h
  letI := h
  letI : IsRegularLocalRing
      ((Spec (CommRingCat.of Closure)).presheaf.stalk finitePoint) :=
    IsRegularLocalRing.of_ringEquiv
      (asIso ((OriginalIntegerClosureGluing318.finiteChart
        OriginalPrimeThreeActualQuotient318.twist).stalkMap finitePoint)).commRingCatIsoToRingEquiv
  apply actual_normalized_point_not_regular
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of Closure) finitePoint).commRingCatIsoToRingEquiv

end OriginalPrimeThreeNonregularSchemePoint318
