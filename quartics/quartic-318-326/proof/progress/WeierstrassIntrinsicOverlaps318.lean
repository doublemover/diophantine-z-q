module
public import WeierstrassIntrinsicSections318
public import FullTripleIntersection318
public import ActualOverlapPullbacks318
public import LocalSectionCompatibility318
public section
noncomputable section
namespace WeierstrassIntrinsicOverlaps318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open WeierstrassIntrinsicSections318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (A B : R)

theorem x_finite :
    (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map
      (homOfLE (show xOpen A B ⊓ finiteOpen A B ≤ xOpen A B from inf_le_left)).op (xSection A B) =
    (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map
      (homOfLE (show xOpen A B ⊓ finiteOpen A B ≤ finiteOpen A B from inf_le_right)).op (finiteSection A B) := by
  let k := Spec.map (CommRingCat.ofHom
    (algebraMap (WeierstrassOverlap318.Affine A B) (FiniteInvariantDifferential318.CommonRing A B))) ≫
      WeierstrassGluing318.finiteChart A B
  have hk : IsOpenImmersion k := open_of_route _ _ k
    (FiniteOverlapSheaves318.x_open A B) (InvariantChartCover318.finiteInto_open A B 0)
    (ActualOverlapPullbacks318.finite_x_route A B)
  exact IntrinsicOverlapSections318.intersection_agreement
    (FiniteInvariantDifferential318.xMap A B) (FiniteInvariantDifferential318.yMap A B)
    (FiniteOverlapSheaves318.x_open A B) (FiniteOverlapSheaves318.y_open A B)
    (InvariantChartCover318.finiteInto A B 0) (InvariantChartCover318.finiteInto A B 1) k
    (WeierstrassGluing318.structureMap A B)
    (IntrinsicFamilyFrames318.finite_structure A B 0) (IntrinsicFamilyFrames318.finite_structure A B 1)
    (structure_of_route _ _ k _ (IntrinsicFamilyFrames318.finite_structure A B 0)
      (ActualOverlapPullbacks318.finite_x_route A B))
    (ActualOverlapPullbacks318.finite_x_route A B) (ActualOverlapPullbacks318.finite_y_route A B)
    (FiniteInvariantDifferential318.xForm A B) (InvariantChartForms318.finite A B)
    (FiniteInvariantDifferential318.invariant_overlap A B).symm
    (image_top_eq_inter _ _ k (ActualChartIntersections318.finite_image A B))

theorem finite_infinity :
    (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map
      (homOfLE (show finiteOpen A B ⊓ infinityOpen A B ≤ finiteOpen A B from inf_le_left)).op (finiteSection A B) =
    (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map
      (homOfLE (show finiteOpen A B ⊓ infinityOpen A B ≤ infinityOpen A B from inf_le_right)).op (infinitySection A B) := by
  let k := FullInfinityIntersection318.into A B
  have hk : IsOpenImmersion k := open_of_route _ _ k
    (ActualInfinityOpen318.finite_open A B) (InvariantChartCover318.finiteInto_open A B 1)
    (FullInfinityIntersection318.finite_route A B)
  exact IntrinsicOverlapSections318.intersection_agreement
    (DifferentialChartMaps318.finiteChartMap A B) (DifferentialChartMaps318.infinityChartMap A B)
    (ActualInfinityOpen318.finite_open A B) (ActualInfinityOpen318.infinity_open A B)
    (InvariantChartCover318.finiteInto A B 1) (InvariantChartCover318.infinityInto A B) k
    (WeierstrassGluing318.structureMap A B)
    (IntrinsicFamilyFrames318.finite_structure A B 1) (IntrinsicFamilyFrames318.infinity_structure A B)
    (structure_of_route _ _ k _ (IntrinsicFamilyFrames318.finite_structure A B 1)
      (FullInfinityIntersection318.finite_route A B))
    (FullInfinityIntersection318.finite_route A B) (FullInfinityIntersection318.infinity_route A B)
    (InvariantChartForms318.finite A B) (InvariantChartForms318.infinity A B)
    (InvariantChartForms318.invariant_overlap A B)
    (image_top_eq_inter _ _ k (FullInfinityIntersection318.full_image A B))

theorem x_infinity (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map
      (homOfLE (show xOpen A B ⊓ infinityOpen A B ≤ xOpen A B from inf_le_left)).op (xSection A B) =
    (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map
      (homOfLE (show xOpen A B ⊓ infinityOpen A B ≤ infinityOpen A B from inf_le_right)).op (infinitySection A B) := by
  apply LocalSectionCompatibility318.trans_of_inter_le _ (xOpen A B) (finiteOpen A B)
    (xSection A B) (finiteSection A B) (infinityOpen A B) (infinitySection A B)
    (x_finite A B) (finite_infinity A B)
  intro p hp
  obtain ⟨a,_,ha⟩ := hp.1
  obtain ⟨b,_,hb⟩ := hp.2
  obtain ⟨q,hq⟩ := FullTripleIntersection318.overlap_in_y A B hD p ⟨a,ha⟩ ⟨b,hb⟩
  exact ⟨q,trivial,hq⟩

end WeierstrassIntrinsicOverlaps318
