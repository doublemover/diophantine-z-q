module
public import ContactOriginalChartIntersection318
public import AffineQuotientPushout318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace ContactProjectiveQuotientData318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
abbrev finiteRing := RelativeOriginalAffineChart318.ring (CommRingCat.of ℚ) R
  (ContactOriginalRelativePolynomialCharts318.finiteRing c)
abbrev infinityRing := RelativeOriginalAffineChart318.ring (CommRingCat.of ℚ) R
  (ContactOriginalRelativePolynomialCharts318.infinityRing c)
abbrev overlapRing := ContactOriginalRelativeOverlap318.ring R c
abbrev finiteArrow : finiteRing R c ⟶ overlapRing R c :=
  RelativeOriginalAffineChartMap318.ringMap (CommRingCat.of ℚ) R
    (ContactOriginalRelativePolynomialCharts318.finiteRing c) (ContactOriginalRelativeOverlap318.oldRing c)
    (ContactOriginalRelativeOverlap318.finiteMap c)
abbrev infinityArrow : infinityRing R c ⟶ overlapRing R c :=
  RelativeOriginalAffineChartMap318.ringMap (CommRingCat.of ℚ) R
    (ContactOriginalRelativePolynomialCharts318.infinityRing c) (ContactOriginalRelativeOverlap318.oldRing c)
    (ContactOriginalRelativeOverlap318.infinityMap c)
/-- Full ideals on the two actual complete original charts, agreeing on
the actual whole Laurent overlap. No local finite/free assumption: an open
chart restriction of a moving finite-flat divisor need not be finite. -/
structure Datum where
  finiteIdeal : Ideal (finiteRing R c)
  infinityIdeal : Ideal (infinityRing R c)
  compatible : Ideal.map (finiteArrow R c).hom finiteIdeal=
    Ideal.map (infinityArrow R c).hom infinityIdeal
variable (D : Datum R c)
abbrev overlapIdeal : Ideal (overlapRing R c) := Ideal.map (finiteArrow R c).hom D.finiteIdeal
abbrev finiteFamily : Scheme := Spec (CommRingCat.of ((finiteRing R c) ⧸ D.finiteIdeal))
abbrev infinityFamily : Scheme := Spec (CommRingCat.of ((infinityRing R c) ⧸ D.infinityIdeal))
abbrev overlapFamily : Scheme := Spec (CommRingCat.of ((overlapRing R c) ⧸ overlapIdeal R c D))
abbrev finiteInto : finiteFamily R c D ⟶ Spec (finiteRing R c) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.finiteIdeal))
abbrev infinityInto : infinityFamily R c D ⟶ Spec (infinityRing R c) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.infinityIdeal))
abbrev overlapInto : overlapFamily R c D ⟶ Spec (overlapRing R c) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (overlapIdeal R c D)))
instance finite_closed : IsClosedImmersion (finiteInto R c D) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
instance infinity_closed : IsClosedImmersion (infinityInto R c D) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
end ContactProjectiveQuotientData318
