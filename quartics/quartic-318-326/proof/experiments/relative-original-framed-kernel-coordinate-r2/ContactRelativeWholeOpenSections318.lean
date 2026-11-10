module
public import ContactOriginalRelativeOverlapSpan318
public import OriginalAffinePathWholeSections318
public section
noncomputable section
namespace ContactRelativeWholeOpenSections318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalRelativeOverlap318 ContactOriginalRelativePolynomialCharts318
open ContactOriginalRelativeLineOverlap318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))

abbrev finiteOpen := (finiteInto R c) ''ᵁ ⊤
abbrev infinityOpen := (infinityInto R c) ''ᵁ ⊤

lemma overlap_image : (into R c) ''ᵁ ⊤ = finiteOpen R c ⊓ infinityOpen R c := by
  simpa only [finiteOpen,infinityOpen,Scheme.Hom.image_top_eq_opensRange,
    ContactOriginalRelativePolynomialCharts318.finite_range,
    ContactOriginalRelativePolynomialCharts318.infinity_range] using full_intersection R c

lemma cover : finiteOpen R c ⊔ infinityOpen R c = ⊤ := by
  simpa only [finiteOpen,infinityOpen,Scheme.Hom.image_top_eq_opensRange] using
    ContactOriginalRelativePolynomialCharts318.cover R c

lemma finite_affine : IsAffineOpen (finiteOpen R c) := by
  rw [finiteOpen,Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _
lemma infinity_affine : IsAffineOpen (infinityOpen R c) := by
  rw [infinityOpen,Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _

/-- Both entire chart-section comparisons use the SAME actual original
line on the test curve, without field or reducedness restrictions. -/
def finiteEquiv : finiteSections R c L ≃+ Γ(L.object,finiteOpen R c) :=
  OriginalOpenPullbackSections318.sectionsEquiv (finiteInto R c) L.object

def infinityEquiv : infinitySections R c L ≃+ Γ(L.object,infinityOpen R c) :=
  OriginalOpenPullbackSections318.sectionsEquiv (infinityInto R c) L.object

/-- The same original Laurent section module, identified with sections of
the SAME line on its full ambient intersection. No choice of basis. -/
@[expose] def overlapEquiv : originalSections R c L ≃+
    Γ(L.object,finiteOpen R c ⊓ infinityOpen R c) :=
  (OriginalOpenPullbackSections318.sectionsEquiv (into R c) L.object).trans
    (L.object.presheaf.mapIso (eqToIso (overlap_image R c).symm).op).addCommGroupIsoToAddEquiv

lemma finite_square (s : finiteSections R c L) :
    overlapEquiv R c L (finiteRestriction R c L s) =
      L.object.presheaf.map (homOfLE inf_le_left :
        finiteOpen R c ⊓ infinityOpen R c ⟶ finiteOpen R c).op (finiteEquiv R c L s) := by
  rw [show finiteRestriction R c L s =
      (finiteComparison R c L).hom.app ⊤
        (OriginalOpenPullbackSections318.sectionPull (finiteEdge R c) (finiteLine R c L).object s) from
    OriginalAffinePathWholeSections318.restriction_direct _ _ _ _ s]
  change L.object.presheaf.map _
    (OriginalOpenPullbackSections318.sectionsEquiv (into R c) L.object _) = _
  rw [OriginalOpenPullbackSections318.nested_path (finiteEdge R c)
    (finiteInto R c) (into R c) (finiteEdge_into R c) L.object s,
    ← Functor.map_comp_apply] <;> rfl

lemma infinity_square (s : infinitySections R c L) :
    overlapEquiv R c L (infinityRestriction R c L s) =
      L.object.presheaf.map (homOfLE inf_le_right :
        finiteOpen R c ⊓ infinityOpen R c ⟶ infinityOpen R c).op (infinityEquiv R c L s) := by
  rw [show infinityRestriction R c L s =
      (infinityComparison R c L).hom.app ⊤
        (OriginalOpenPullbackSections318.sectionPull (infinityEdge R c) (infinityLine R c L).object s) from
    OriginalAffinePathWholeSections318.restriction_direct _ _ _ _ s]
  change L.object.presheaf.map _
    (OriginalOpenPullbackSections318.sectionsEquiv (into R c) L.object _) = _
  rw [OriginalOpenPullbackSections318.nested_path (infinityEdge R c)
    (infinityInto R c) (into R c) (infinityEdge_into R c) L.object s,
    ← Functor.map_comp_apply] <;> rfl
end ContactRelativeWholeOpenSections318
