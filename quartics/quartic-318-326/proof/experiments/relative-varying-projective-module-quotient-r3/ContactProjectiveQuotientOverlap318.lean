module
public import ContactProjectiveQuotientData318
public section
noncomputable section
namespace ContactProjectiveQuotientOverlap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveQuotientData318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (D : Datum R c)
@[expose] def finiteMap : overlapFamily R c D ⟶ finiteFamily R c D :=
  Spec.map (AffineQuotientPushout318.arrow (finiteArrow R c) D.finiteIdeal (overlapIdeal R c D) rfl)
@[expose] def infinityMap : overlapFamily R c D ⟶ infinityFamily R c D :=
  Spec.map (AffineQuotientPushout318.arrow (infinityArrow R c) D.infinityIdeal
    (overlapIdeal R c D) D.compatible.symm)
lemma finite_cartesian : IsPullback (finiteMap R c D) (overlapInto R c D)
    (finiteInto R c D) (ContactOriginalRelativeOverlap318.finiteEdge R c) :=
  (AffineQuotientPushout318.pullback (finiteArrow R c) D.finiteIdeal (overlapIdeal R c D) rfl).flip
lemma infinity_cartesian : IsPullback (infinityMap R c D) (overlapInto R c D)
    (infinityInto R c D) (ContactOriginalRelativeOverlap318.infinityEdge R c) :=
  (AffineQuotientPushout318.pullback (infinityArrow R c) D.infinityIdeal
    (overlapIdeal R c D) D.compatible.symm).flip
instance finite_open : IsOpenImmersion (finiteMap R c D) :=
  MorphismProperty.of_isPullback (finite_cartesian R c D).flip inferInstance
instance infinity_open : IsOpenImmersion (infinityMap R c D) :=
  MorphismProperty.of_isPullback (infinity_cartesian R c D).flip inferInstance
end ContactProjectiveQuotientOverlap318
