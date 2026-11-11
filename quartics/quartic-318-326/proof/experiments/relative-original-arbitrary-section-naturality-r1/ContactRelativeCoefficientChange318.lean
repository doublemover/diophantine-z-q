module
public import RelativeCoefficientChange318
public import ContactOriginalRelativeLineOverlap318
public section
noncomputable section
namespace ContactRelativeCoefficientChange318
open AlgebraicGeometry CategoryTheory
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ)

abbrev curveMap : curve S c ⟶ curve R c :=
  RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) R S f
    (ContactOriginalAffineTestCover318.p c)
abbrev finiteRingMap := RelativeCoefficientChange318.ringMap (CommRingCat.of ℚ)
  R S (finiteRing c) f
abbrev infinityRingMap := RelativeCoefficientChange318.ringMap (CommRingCat.of ℚ)
  R S (infinityRing c) f
abbrev overlapRingMap := RelativeCoefficientChange318.ringMap (CommRingCat.of ℚ)
  R S (oldRing c) f

@[reassoc] lemma finite_square : Spec.map (finiteRingMap R S f c) ≫ finiteInto R c =
    finiteInto S c ≫ curveMap R S f c :=
  RelativeCoefficientChange318.into_square _ _ _ _ _ _ _ _
@[reassoc] lemma infinity_square : Spec.map (infinityRingMap R S f c) ≫ infinityInto R c =
    infinityInto S c ≫ curveMap R S f c :=
  RelativeCoefficientChange318.into_square _ _ _ _ _ _ _ _
@[reassoc] lemma overlap_square : Spec.map (overlapRingMap R S f c) ≫ into R c =
    into S c ≫ curveMap R S f c :=
  RelativeCoefficientChange318.into_square _ _ _ _ _ _ _ _

/-- These are the actual original affine restrictions, not new arrows
chosen to make cohomology commute. -/
lemma finite_ring_square : ContactOriginalRelativeLineOverlap318.finiteArrow R c ≫
    overlapRingMap R S f c = finiteRingMap R S f c ≫
      ContactOriginalRelativeLineOverlap318.finiteArrow S c :=
  RelativeCoefficientChange318.edge_square _ _ _ _ _ _ _
lemma infinity_ring_square : ContactOriginalRelativeLineOverlap318.infinityArrow R c ≫
    overlapRingMap R S f c = infinityRingMap R S f c ≫
      ContactOriginalRelativeLineOverlap318.infinityArrow S c :=
  RelativeCoefficientChange318.edge_square _ _ _ _ _ _ _

@[reassoc] lemma finite_edge_square : Spec.map (overlapRingMap R S f c) ≫ finiteEdge R c =
    finiteEdge S c ≫ Spec.map (finiteRingMap R S f c) := by
  rw [← Spec.map_comp,← Spec.map_comp,finite_ring_square]
@[reassoc] lemma infinity_edge_square : Spec.map (overlapRingMap R S f c) ≫ infinityEdge R c =
    infinityEdge S c ≫ Spec.map (infinityRingMap R S f c) := by
  rw [← Spec.map_comp,← Spec.map_comp,infinity_ring_square]
end ContactRelativeCoefficientChange318
