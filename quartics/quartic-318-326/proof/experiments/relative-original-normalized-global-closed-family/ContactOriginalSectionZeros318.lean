module
public import OriginalAffineSectionZero318
public import ContactRelativeOriginalHZero318
public section
noncomputable section
namespace ContactOriginalSectionZeros318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalRelativeOverlap318 ContactOriginalCoefficientActions318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
variable (s : Γ(L.object,⊤))

@[expose] def finiteSection : OriginalLineAffineModel318.sections (CommRingCat.of (R ⊗[ℚ] finiteRing c))
    (finiteLine R c L) := (ContactRelativeOriginalHZero318.pair R c L s).1
@[expose] def infinitySection : OriginalLineAffineModel318.sections (CommRingCat.of (R ⊗[ℚ] infinityRing c))
    (infinityLine R c L) := (ContactRelativeOriginalHZero318.pair R c L s).2
@[expose] def overlapSection : originalSections R c L := finiteRestriction R c L (finiteSection R c L s)

lemma original_overlap : overlapSection R c L s=infinityRestriction R c L (infinitySection R c L s) :=
  sub_eq_zero.mp (ContactRelativeOriginalHZero318.compatible R c L s)

@[expose] def finiteIdeal : Ideal (R ⊗[ℚ] finiteRing c) :=
  OriginalAffineSectionZero318.ideal _ (finiteLine R c L) (finiteSection R c L s)
@[expose] def infinityIdeal : Ideal (R ⊗[ℚ] infinityRing c) :=
  OriginalAffineSectionZero318.ideal _ (infinityLine R c L) (infinitySection R c L s)
@[expose] def overlapIdeal : Ideal (ring R c) :=
  OriginalAffineSectionZero318.ideal (ring R c) (line R c L) (overlapSection R c L s)

/-- The exact original zero ideal extends over the whole ACTUAL finite
intersection, through the original line path, not a pointwise zero test. -/
lemma finite_overlap : overlapIdeal R c L s=Ideal.map (finiteArrow R c).hom (finiteIdeal R c L s) :=
  OriginalAffineSectionZero318.along_path (finiteArrow R c) (finiteLine R c L) (line R c L)
    (finiteComparison R c L) (finiteSection R c L s)

lemma infinity_overlap : overlapIdeal R c L s=Ideal.map (infinityArrow R c).hom (infinityIdeal R c L s) := by
  change OriginalAffineSectionZero318.ideal (ring R c) (line R c L) (overlapSection R c L s)=_
  rw [original_overlap]
  exact OriginalAffineSectionZero318.along_path (infinityArrow R c) (infinityLine R c L) (line R c L)
    (infinityComparison R c L) (infinitySection R c L s)

/-- Both whole-chart zero ideals agree on the SAME original Laurent
intersection. This is the concrete ideal gluing prerequisite. -/
lemma same_overlap : Ideal.map (finiteArrow R c).hom (finiteIdeal R c L s)=
    Ideal.map (infinityArrow R c).hom (infinityIdeal R c L s) :=
  (finite_overlap R c L s).symm.trans (infinity_overlap R c L s)

@[expose] def finiteZero : Scheme := Spec (CommRingCat.of ((R ⊗[ℚ] finiteRing c) ⧸ finiteIdeal R c L s))
@[expose] def infinityZero : Scheme := Spec (CommRingCat.of ((R ⊗[ℚ] infinityRing c) ⧸ infinityIdeal R c L s))
@[expose] def overlapZero : Scheme := Spec (CommRingCat.of ((ring R c) ⧸ overlapIdeal R c L s))
end ContactOriginalSectionZeros318
