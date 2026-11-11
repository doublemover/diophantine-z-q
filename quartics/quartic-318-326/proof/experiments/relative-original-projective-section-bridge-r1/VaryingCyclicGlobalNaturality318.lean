module
public import VaryingCyclicGlobalClassifyingMap318
public section
noncomputable section
namespace VaryingCyclicGlobalNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingSourceFreeQuotientClassifier318 VaryingCyclicCoefficientSections318
open VaryingCyclicGlobalClassifyingMap318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S) (w : ι → List A)
variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
local notation "δ" => VaryingCyclicDeterminantCover318.delta R A ι S a w
local notation "L" => VaryingCyclicDeterminantCover318.ring R A ι S a w
local notation "aT" => mapCyclic R A ι S a T f
variable (h : IsUnit (f δ))
@[expose] def lift : L →ₐ[R] T := IsLocalization.Away.liftAlgHom δ h
lemma lift_base : (lift R A ι S a w T f h).comp
    (VaryingCyclicDeterminantCover318.coefficient R A ι S a w)=f := by
  ext s
  exact IsLocalization.Away.lift_eq δ h s
lemma test_unit : IsUnit (VaryingMatrixWords318.determinant
    (VaryingSourceActionClassifier318.point R A ι T aT.data).val w) := by
  rw [← VaryingSourceSurjectiveCoefficient318.determinant_map R A ι S T f a.data w]
  exact h

/-- Whenever an original determinant becomes invertible on any test,
the global map restricts to the actual normalized classifying chart. -/
lemma test_formula : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ classify R A ι S a=
    VaryingCyclicNormalizedChart318.schemeMap R A ι T aT w (test_unit R A ι S a w T f h) := by
  let g := lift R A ι S a w T f h
  have hf : Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (VaryingCyclicDeterminantCover318.cover R A ι S a).f w=
      Spec.map (CommRingCat.ofHom f.toRingHom) := by
    change Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom
      (VaryingCyclicDeterminantCover318.coefficient R A ι S a w).toRingHom)=_
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (g.comp
      (VaryingCyclicDeterminantCover318.coefficient R A ι S a w)).toRingHom)=_
    rw [lift_base]
  have hc : mapCyclic R A ι L (VaryingCyclicDeterminantCover318.localized R A ι S a w) T g=aT := by
    change mapCyclic R A ι L (mapCyclic R A ι S a L
      (VaryingCyclicDeterminantCover318.coefficient R A ι S a w)) T g=aT
    rw [VaryingCyclicCoefficientComposition318.map_comp,lift_base]
  rw [← hf,Category.assoc,chart_classify]
  have hn := VaryingCyclicPointNaturality318.schemeMap_natural R A ι w L
    (VaryingCyclicDeterminantCover318.localized R A ι S a w)
    (VaryingCyclicDeterminantCover318.unit R A ι S a w) T g
  simpa only [hc] using hn

/-- Global classifying maps commute with EVERY coefficient homomorphism,
proved on the entire target determinant cover, not just field points. -/
lemma natural : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ classify R A ι S a=classify R A ι T aT := by
  apply Scheme.Cover.hom_ext (VaryingCyclicDeterminantCover318.cover R A ι T aT) _ _
  intro v
  let U := VaryingCyclicDeterminantCover318.ring R A ι T aT v
  let g := VaryingCyclicDeterminantCover318.coefficient R A ι T aT v
  have hu : IsUnit ((g.comp f) (VaryingCyclicDeterminantCover318.delta R A ι S a v)) := by
    change IsUnit (g (f (VaryingMatrixWords318.determinant
      (VaryingSourceActionClassifier318.point R A ι S a.data).val v)))
    rw [VaryingSourceSurjectiveCoefficient318.determinant_map]
    exact IsLocalization.Away.algebraMap_isUnit (VaryingCyclicDeterminantCover318.delta R A ι T aT v)
  rw [chart_classify,← Category.assoc]
  change (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) ≫
    classify R A ι S a=VaryingCyclicDeterminantCover318.localMap R A ι T aT v
  rw [← Spec.map_comp]
  have ht := test_formula R A ι S a v U (g.comp f) hu
  simpa only [VaryingCyclicDeterminantCover318.localMap,VaryingCyclicDeterminantCover318.localized,
    VaryingCyclicCoefficientComposition318.map_comp] using ht
end VaryingCyclicGlobalNaturality318
