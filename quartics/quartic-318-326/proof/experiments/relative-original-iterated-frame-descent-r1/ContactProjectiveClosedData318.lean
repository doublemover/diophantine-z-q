module
public import ContactProjectiveQuotientIdealSheaf318
public import AffineClosedRestriction318
public section
noncomputable section
namespace ContactProjectiveClosedData318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveQuotientData318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  {Z : Scheme.{0}} (p : Z ⟶ ContactOriginalRelativePolynomialCharts318.curve R c) [IsClosedImmersion p]
local notation "i" => ContactOriginalRelativePolynomialCharts318.finiteInto R c
local notation "j" => ContactOriginalRelativePolynomialCharts318.infinityInto R c
abbrev finiteIdeal : Ideal (finiteRing R c) := AffineClosedRestriction318.ideal p (finiteRing R c) i
abbrev infinityIdeal : Ideal (infinityRing R c) := AffineClosedRestriction318.ideal p (infinityRing R c) j
lemma compatible : Ideal.map (finiteArrow R c).hom (finiteIdeal R c p)=
    Ideal.map (infinityArrow R c).hom (infinityIdeal R c p) := by
  have hf := AffineClosedRestriction318.ideal_map p (finiteRing R c) i
    (overlapRing R c) (finiteArrow R c)
  have hi := AffineClosedRestriction318.ideal_map p (infinityRing R c) j
    (overlapRing R c) (infinityArrow R c)
  change AffineClosedRestriction318.ideal p (overlapRing R c)
    (ContactOriginalRelativeOverlap318.finiteEdge R c ≫ i)=_ at hf
  change AffineClosedRestriction318.ideal p (overlapRing R c)
    (ContactOriginalRelativeOverlap318.infinityEdge R c ≫ j)=_ at hi
  rw [ContactOriginalRelativeOverlap318.finiteEdge_into] at hf
  rw [ContactOriginalRelativeOverlap318.infinityEdge_into] at hi
  exact hf.symm.trans hi
/-- EVERY closed subscheme of the actual original projective curve,
without any finite/free restriction on its affine pieces, supplies datum. -/
@[expose] def datum : Datum R c where
  finiteIdeal := finiteIdeal R c p
  infinityIdeal := infinityIdeal R c p
  compatible := compatible R c p
end ContactProjectiveClosedData318
