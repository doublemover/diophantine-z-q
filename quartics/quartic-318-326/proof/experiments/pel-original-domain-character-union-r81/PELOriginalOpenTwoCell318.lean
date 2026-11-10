module
public import PELOriginalDiskCharacteristic318
public import QuotientSingletonOpenEmbedding318
public section
noncomputable section
namespace PELOriginalOpenTwoCell318
open Set Metric Topology
open PELOriginalDiskCharacteristic318 PELUnlevelledComplexBase318

instance closedDiskCompact : CompactSpace ClosedDisk :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℝ × ℝ) 1)

@[expose] def diskInterior : Set ClosedDisk := {z | z.val∈ball 0 1}

theorem characteristic_quotient : IsQuotientMap characteristic :=
  IsQuotientMap.of_surjective_continuous characteristic_surjective characteristic_continuous

theorem interior_open_embedding :
    IsOpenEmbedding (fun z : diskInterior => characteristic z.val) :=
  QuotientSingletonOpenEmbedding318.restriction characteristic characteristic_quotient diskInterior
    (isOpen_ball.preimage continuous_subtype_val) (fun z hz w h => interior_point_unique z w hz h)

theorem interior_range : Set.range (fun z : diskInterior => characteristic z.val)=openCell := by
  ext y
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z.val,z.property,hz⟩
  · rintro ⟨z,hz,hzy⟩
    exact ⟨⟨z,hz⟩,hzy⟩

theorem actual_openCell_open : IsOpen openCell := by
  rw [←interior_range]
  exact interior_open_embedding.isOpenMap.isOpen_range

@[expose] def standardDiskInterior : ball (0:ℝ × ℝ) 1 ≃ₜ diskInterior where
  toFun z := ⟨⟨z.val,z.property.le⟩,z.property⟩
  invFun z := ⟨z.val.val,z.property⟩
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- A genuine open2-cell, with inverse continuity, on the original
arithmetic curve. This is not merely a continuous injective parametrization. -/
@[expose] def originalOpenTwoCell : ball (0:ℝ × ℝ) 1 ≃ₜ openCell :=
  standardDiskInterior.trans (interior_open_embedding.toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr interior_range))
end PELOriginalOpenTwoCell318
