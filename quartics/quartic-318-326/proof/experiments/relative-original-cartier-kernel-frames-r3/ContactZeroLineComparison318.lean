module
public import SectionZeroEquivalence318
public import ContactHZeroGeometricUnit318
public import ContactZeroCoefficientCharts318
public section
noncomputable section
namespace ContactZeroLineComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalSectionZeros318 OriginalSectionPullbackComposition318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L N : Line (curve R c)) (a : L.object ≅ N.object) (s : Γ(L.object,⊤))
abbrev section := a.hom.app ⊤ s

lemma finite_section : finiteSection R c N (section R c L N a s) =
    ((Scheme.Modules.pullback (finiteInto R c)).map a.hom).app ⊤ (finiteSection R c L s) := by
  change (ContactRelativeOriginalHZero318.pair R c N (a.hom.app ⊤ s)).1 = _
  rw [ContactHZeroGeometricUnit318.finite_pair]
  change pull (finiteInto R c) N.object (a.hom.app ⊤ s) =
    ((Scheme.Modules.pullback (finiteInto R c)).map a.hom).app ⊤
      (ContactRelativeOriginalHZero318.pair R c L s).1
  rw [ContactHZeroGeometricUnit318.finite_pair]
  exact (OriginalSectionPullbackComposition318.naturality (finiteInto R c) a.hom s).symm
lemma infinity_section : infinitySection R c N (section R c L N a s) =
    ((Scheme.Modules.pullback (infinityInto R c)).map a.hom).app ⊤ (infinitySection R c L s) := by
  change (ContactRelativeOriginalHZero318.pair R c N (a.hom.app ⊤ s)).2 = _
  rw [ContactHZeroGeometricUnit318.infinity_pair]
  change pull (infinityInto R c) N.object (a.hom.app ⊤ s) =
    ((Scheme.Modules.pullback (infinityInto R c)).map a.hom).app ⊤
      (ContactRelativeOriginalHZero318.pair R c L s).2
  rw [ContactHZeroGeometricUnit318.infinity_pair]
  exact (OriginalSectionPullbackComposition318.naturality (infinityInto R c) a.hom s).symm

/-- Same original chart ring and same literal ideal after the genuine
line comparison, not merely an isomorphism of abstract zero sets. -/
lemma finite_ideal : finiteIdeal R c N (section R c L N a s) = finiteIdeal R c L s := by
  change OriginalAffineSectionZero318.ideal _ _ (finiteSection R c N _) = _
  rw [finite_section]
  exact SectionZeroEquivalence318.original_affine _ (finiteLine R c L) (finiteLine R c N)
    ((Scheme.Modules.pullback (finiteInto R c)).mapIso a) (finiteSection R c L s)
lemma infinity_ideal : infinityIdeal R c N (section R c L N a s) = infinityIdeal R c L s := by
  change OriginalAffineSectionZero318.ideal _ _ (infinitySection R c N _) = _
  rw [infinity_section]
  exact SectionZeroEquivalence318.original_affine _ (infinityLine R c L) (infinityLine R c N)
    ((Scheme.Modules.pullback (infinityInto R c)).mapIso a) (infinitySection R c L s)
lemma overlap_ideal : overlapIdeal R c N (section R c L N a s) = overlapIdeal R c L s := by
  rw [ContactOriginalSectionZeros318.finite_overlap,ContactOriginalSectionZeros318.finite_overlap,finite_ideal]
end ContactZeroLineComparison318
