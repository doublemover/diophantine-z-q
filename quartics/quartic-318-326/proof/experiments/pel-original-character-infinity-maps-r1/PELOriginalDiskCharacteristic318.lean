module
public import PELOriginalPolygonDisk318
public section
noncomputable section
namespace PELOriginalDiskCharacteristic318
open Set Metric
open PELOriginalPolygonDisk318 PELOriginalDirichletPolygon318 PELActualPolygonHomeomorph318
open PELOriginalSideQuotient318 PELUnlevelledComplexBase318
open PELStrictPolygonExtension318 PELOriginalInteriorUniqueness318
open PELDirichletHeight318 PELEffectiveNormOneAction318
set_option maxHeartbeats 1800000
abbrev ClosedDisk := closedBall (0:ℝ × ℝ) 1

@[expose] def diskOriginalHomeomorph : ClosedDisk ≃ₜ originalDomain :=
  closedDiskPolygonHomeomorph.trans originalPolygonHomeomorph.symm

theorem disk_original_strict (z : ClosedDisk) (hz : z.val∈ball 0 1) :
    strictInequalities (scaledFirst (diskOriginalHomeomorph z).val)
      (scaledSecond (diskOriginalHomeomorph z).val) := by
  have hs := diskPoint_strict z hz
  change strictInequalities
    (scaledFirst (polygonInverse (closedDiskPolygonHomeomorph z)).val)
    (scaledSecond (polygonInverse (closedDiskPolygonHomeomorph z)).val)
  rw [(inverse_scaled _).1,(inverse_scaled _).2]
  exact hs

/-- Genuine continuous characteristic map from the closed standard2-disk
onto the SAME original arithmetic curve, with all boundary identifications
retained. It is not asserted globally injective. -/
@[expose] def characteristic (z : ClosedDisk) : UnlevelledBase :=
  projection (diskOriginalHomeomorph z).val

theorem characteristic_continuous : Continuous characteristic :=
  projection_holomorphic.continuous.comp
    (continuous_subtype_val.comp diskOriginalHomeomorph.continuous)

theorem characteristic_surjective : Function.Surjective characteristic := by
  change Function.Surjective (arithmeticComparison ∘ polygonProjection ∘ diskOriginalHomeomorph)
  exact arithmeticComparison_surjective.comp
    (Quotient.mk_surjective.comp diskOriginalHomeomorph.surjective)

/-- An interior point has NO other closed-disk representative, including a
boundary representative. The proof uses full original strict uniqueness. -/
theorem interior_point_unique (z w : ClosedDisk) (hz : z.val∈ball 0 1)
    (h : characteristic z=characteristic w) : z=w := by
  have hs := disk_original_strict z hz
  change projection (diskOriginalHomeomorph z).val=
    projection (diskOriginalHomeomorph w).val at h
  obtain ⟨g,hg⟩ := (show ∃ g : effectiveGroup,
    g • (diskOriginalHomeomorph z).val=(diskOriginalHomeomorph w).val from Quotient.exact h.symm)
  obtain ⟨u,rfl⟩ := effectiveMap_surjective g
  have hi := strict_representative_unique (diskOriginalHomeomorph z).val u hs
    (by rw [hg]; exact (diskOriginalHomeomorph w).property)
  apply diskOriginalHomeomorph.injective
  exact Subtype.ext (hi.symm.trans hg)

@[expose] def openCell : Set UnlevelledBase := characteristic '' {z : ClosedDisk | z.val∈ball 0 1}
@[expose] def attachingImage : Set UnlevelledBase :=
  characteristic '' {z : ClosedDisk | z.val∈sphere 0 1}

theorem open_attaching_disjoint : Disjoint openCell attachingImage := by
  rw [Set.disjoint_left]
  intro y hy hf
  obtain ⟨z,hz,hzy⟩ := hy
  obtain ⟨w,hw,hwy⟩ := hf
  have hzw := interior_point_unique z w hz (hzy.trans hwy.symm)
  have hlt : dist z.val 0<1 := hz
  have heq : dist w.val 0=1 := hw
  rw [hzw] at hlt
  exact (ne_of_lt hlt) heq

/-- The whole original curve is the disjoint union of this actual open
2-cell image and the actual attaching-circle image. This is characteristic
map data, not yet a CW structure or an Euler/genus theorem. -/
theorem whole_curve : openCell ∪ attachingImage=Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨z,rfl⟩ := characteristic_surjective y
  have hz : dist z.val 0≤1 := z.property
  rcases lt_or_eq_of_le hz with hi | hf
  · exact Or.inl ⟨z,hi,rfl⟩
  · exact Or.inr ⟨z,hf,rfl⟩
end PELOriginalDiskCharacteristic318
