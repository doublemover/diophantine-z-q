module
public import RelativeOriginalAffineChart318
public import ContactOriginalAffineTestCover318
public section
noncomputable section
namespace ContactOriginalRelativePolynomialCharts318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalAffineTestCover318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)

/-- Structural maps to Spec Q are determined by their literal rational
ring maps; this identifies the actual original chart structural arrows. -/
lemma rational_structure_unique {Y : Scheme.{0}}
    (f g : Y ⟶ Spec (CommRingCat.of ℚ)) : f = g := by
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv).mp
  apply CommRingCat.hom_ext
  exact RingHom.ext_rat _ _

abbrev baseMap := Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
abbrev curve := family c (baseMap R)
abbrev finiteRing := CommRingCat.of (ContactKummerOrder318.SourceOrder c)
abbrev infinityRing := CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)

/-- The actual reciprocal integral closure is already a Q[X]-algebra.
Expose its rational scalar structure through that SAME polynomial map. -/
@[expose] instance infinityRationalAlgebra : Algebra ℚ (infinityRing c) :=
  ((algebraMap (Polynomial ℚ) (infinityRing c)).comp
    (algebraMap ℚ (Polynomial ℚ))).toAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
local instance : IsScalarTower ℚ (Polynomial ℚ) (finiteRing c) :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := Polynomial ℚ) (A := finiteRing c)
    (RingHom.ext_rat _ _)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
local instance : IsScalarTower ℚ (Polynomial ℚ) (infinityRing c) :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := Polynomial ℚ) (A := infinityRing c) rfl
local instance : Module.Finite (Polynomial ℚ) (finiteRing c) :=
  (ContactKummerOrder318.source_finite_free c).1

lemma finite_over : SourceGlobalAffine318.chartEmbedding c ≫ p c =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (finiteRing c))) :=
  rational_structure_unique _ _
lemma infinity_over : ContactWholeInfinityScheme318.into c ≫ p c =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (infinityRing c))) :=
  rational_structure_unique _ _

/-- Both ACTUAL complete polynomial charts after arbitrary coefficient
base change. Their rings are the genuine R tensor original-chart rings. -/
abbrev finiteInto := RelativeOriginalAffineChart318.into (CommRingCat.of ℚ) R (finiteRing c)
  (p c) (SourceGlobalAffine318.chartEmbedding c) (finite_over c)
abbrev infinityInto := RelativeOriginalAffineChart318.into (CommRingCat.of ℚ) R (infinityRing c)
  (p c) (ContactWholeInfinityScheme318.into c) (infinity_over c)

lemma finite_range : (finiteInto R c).opensRange = finiteTest c (baseMap R) :=
  RelativeOriginalAffineChart318.range (CommRingCat.of ℚ) R (finiteRing c)
    (p c) (SourceGlobalAffine318.chartEmbedding c) (finite_over c)
lemma infinity_range : (infinityInto R c).opensRange = infinityTest c (baseMap R) :=
  RelativeOriginalAffineChart318.range (CommRingCat.of ℚ) R (infinityRing c)
    (p c) (ContactWholeInfinityScheme318.into c) (infinity_over c)
lemma cover : (finiteInto R c).opensRange ⊔ (infinityInto R c).opensRange = ⊤ := by
  rw [finite_range,infinity_range]
  exact test_cover c (baseMap R)

variable (L : Line (curve R c))
/-- Sections of the SAME original global line on the WHOLE finite chart. -/
abbrev finiteSections := RelativeOriginalAffineChart318.sections
  (CommRingCat.of ℚ) R (finiteRing c) (p c)
  (SourceGlobalAffine318.chartEmbedding c) (finite_over c) L
/-- Sections of the SAME original global line on the WHOLE infinity chart,
with the original reciprocal coordinate, not the finite coordinate reused. -/
abbrev infinitySections := RelativeOriginalAffineChart318.sections
  (CommRingCat.of ℚ) R (infinityRing c) (p c)
  (ContactWholeInfinityScheme318.into c) (infinity_over c) L

instance finiteSections_finite : Module.Finite (Polynomial R) (finiteSections R c L) :=
  RelativeOriginalAffineChart318.finite (CommRingCat.of ℚ) R (finiteRing c) (p c)
    (SourceGlobalAffine318.chartEmbedding c) (finite_over c) L
instance infinitySections_finite : Module.Finite (Polynomial R) (infinitySections R c L) :=
  RelativeOriginalAffineChart318.finite (CommRingCat.of ℚ) R (infinityRing c) (p c)
    (ContactWholeInfinityScheme318.into c) (infinity_over c) L
end ContactOriginalRelativePolynomialCharts318
