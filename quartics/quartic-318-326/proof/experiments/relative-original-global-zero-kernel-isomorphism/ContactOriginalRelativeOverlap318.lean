module
public import RelativeOriginalAffineChartMap318
public import ContactOriginalRelativePolynomialCharts318
public import ContactOverlapTensorCharts318
public section
noncomputable section
namespace ContactOriginalRelativeOverlap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
abbrev oldRing := CommRingCat.of (ContactOverlapTensorCharts318.finiteRing c)
abbrev oldInto := (ContactOverlapTensorCharts318.finiteIso c).inv ≫
  ContactOriginalLaurentOverlap318.into c
abbrev oldFiniteEdge := (ContactOverlapTensorCharts318.finiteIso c).inv ≫
  ContactOriginalLaurentOverlap318.finiteEdge c
abbrev oldInfinityEdge := (ContactOverlapTensorCharts318.finiteIso c).inv ≫
  ContactOriginalLaurentOverlap318.infinityEdge c

/-- The actual affine ring map of an original scheme arrow, retaining its
rational coefficients by uniqueness, not by a chosen coordinate formula. -/
def rationalMap {B O : CommRingCat.{0}} [Algebra ℚ B] [Algebra ℚ O]
    (f : Spec O ⟶ Spec B) : B →ₐ[ℚ] O where
  __ := (Spec.preimage f).hom
  commutes' q := by
    change ((Spec.preimage f).hom.comp (algebraMap ℚ B)) q = algebraMap ℚ O q
    exact RingHom.congr_fun (RingHom.ext_rat _ _) q

lemma rationalMap_spec {B O : CommRingCat.{0}} [Algebra ℚ B] [Algebra ℚ O]
    (f : Spec O ⟶ Spec B) : Spec.map (CommRingCat.ofHom (rationalMap f).toRingHom) = f :=
  Spec.map_preimage f

abbrev finiteMap := rationalMap (oldFiniteEdge c)
abbrev infinityMap := rationalMap (oldInfinityEdge c)

lemma old_over : oldInto c ≫ ContactOriginalAffineTestCover318.p c =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (oldRing c))) :=
  ContactOriginalRelativePolynomialCharts318.rational_structure_unique _ _

/-- The actual complete common Laurent overlap in the SAME original
p-first family on an arbitrary coefficient-ring test. -/
abbrev into := RelativeOriginalAffineChart318.into (CommRingCat.of ℚ) R (oldRing c)
  (ContactOriginalAffineTestCover318.p c) (oldInto c) (old_over c)
abbrev ring := CommRingCat.of (R ⊗[ℚ] oldRing c)

instance : IsOpenImmersion (into R c) := inferInstance

/-- No part of the old intersection is lost on a nonreduced test. -/
lemma full_intersection : (into R c).opensRange =
    ContactOriginalAffineTestCover318.finiteTest c (ContactOriginalRelativePolynomialCharts318.baseMap R) ⊓
      ContactOriginalAffineTestCover318.infinityTest c (ContactOriginalRelativePolynomialCharts318.baseMap R) := by
  rw [RelativeOriginalAffineChart318.range]
  rw [show (oldInto c).opensRange = (ContactOriginalLaurentOverlap318.into c).opensRange from
    Scheme.Hom.opensRange_comp_of_isIso _ _]
  rw [ContactOriginalLaurentOverlap318.full_intersection,Scheme.Hom.preimage_inf] <;> rfl

abbrev finiteEdge := Spec.map (RelativeOriginalAffineChartMap318.ringMap
  (CommRingCat.of ℚ) R (ContactOriginalRelativePolynomialCharts318.finiteRing c) (oldRing c) (finiteMap c))
abbrev infinityEdge := Spec.map (RelativeOriginalAffineChartMap318.ringMap
  (CommRingCat.of ℚ) R (ContactOriginalRelativePolynomialCharts318.infinityRing c) (oldRing c) (infinityMap c))

@[reassoc] lemma finiteEdge_into : finiteEdge R c ≫
    ContactOriginalRelativePolynomialCharts318.finiteInto R c = into R c := by
  apply RelativeOriginalAffineChartMap318.into_square
  rw [rationalMap_spec]
  dsimp only [oldFiniteEdge,oldInto]
  rw [Category.assoc,ContactOriginalLaurentOverlap318.finiteEdge_into]

@[reassoc] lemma infinityEdge_into : infinityEdge R c ≫
    ContactOriginalRelativePolynomialCharts318.infinityInto R c = into R c := by
  apply RelativeOriginalAffineChartMap318.into_square
  rw [rationalMap_spec]
  dsimp only [oldInfinityEdge,oldInto]
  rw [Category.assoc,ContactOriginalLaurentOverlap318.infinityEdge_into]

instance : IsOpenImmersion (finiteEdge R c) := by
  haveI : IsOpenImmersion (finiteEdge R c ≫
      ContactOriginalRelativePolynomialCharts318.finiteInto R c) := by
    rw [finiteEdge_into]
    infer_instance
  exact IsOpenImmersion.of_comp _ _
instance : IsOpenImmersion (infinityEdge R c) := by
  haveI : IsOpenImmersion (infinityEdge R c ≫
      ContactOriginalRelativePolynomialCharts318.infinityInto R c) := by
    rw [infinityEdge_into]
    infer_instance
  exact IsOpenImmersion.of_comp _ _
end ContactOriginalRelativeOverlap318
