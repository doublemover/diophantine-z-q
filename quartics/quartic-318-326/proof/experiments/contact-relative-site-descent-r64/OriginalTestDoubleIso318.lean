module
public import OriginalTestCechCoordinates318
public section
noncomputable section
namespace OriginalTestDoubleIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassBaseChange318 ActualOverlapDiagram318 OriginalTestCechCoordinates318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T T' : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (b' : T' ⟶ B)
  (g : T' ⟶ T) (hg : g ≫ b = b')
abbrev base := first g ≫ b'
abbrev Test := pullback q (base b' g)

/-- The original categorical double maps to the full original family test
by its original curve coordinate and its original base-double projection. -/
@[expose] def hom : Double (f q b b' g hg) ⟶ Test q b' g :=
  pullback.lift (first (f q b b' g hg) ≫ pullback.fst q b')
    (doubleProjection q b b' g hg) (by
      calc
        _ = (first (f q b b' g hg) ≫ p' q b') ≫ b' := by
          simpa only [Category.assoc] using congrArg
            (fun a => first (f q b b' g hg) ≫ a) (pullback.condition (f:=q) (g:=b'))
        _ = (doubleProjection q b b' g hg ≫ first g) ≫ b' :=
          congrArg (fun a => a ≫ b') (OriginalTestCechCoordinates318.double_first q b b' g hg).symm
        _ = _ := Category.assoc _ _ _)
@[reassoc] lemma hom_fst : hom q b b' g hg ≫ pullback.fst q (base b' g) =
    first (f q b b' g hg) ≫ pullback.fst q b' := pullback.lift_fst _ _ _
@[reassoc] lemma hom_snd : hom q b b' g hg ≫ pullback.snd q (base b' g) =
    doubleProjection q b b' g hg := pullback.lift_snd _ _ _

@[expose] def firstLift : Test q b' g ⟶ pullback q b' :=
  testLift q b' (pullback.fst q (base b' g)) (pullback.snd q (base b' g) ≫ first g)
    (by simpa only [Category.assoc] using (pullback.condition (f:=q) (g:=base b' g)))
@[expose] def secondLift : Test q b' g ⟶ pullback q b' :=
  testLift q b' (pullback.fst q (base b' g)) (pullback.snd q (base b' g) ≫ second g)
    (by
      have he := base_equal b b' g hg (first g) (second g) (edge_condition g)
      simpa only [Category.assoc,he] using (pullback.condition (f:=q) (g:=base b' g)))
@[reassoc] lemma firstLift_fst : firstLift q b' g ≫ pullback.fst q b' =
    pullback.fst q (base b' g) := testLift_fst _ _ _ _ _
@[reassoc] lemma firstLift_snd : firstLift q b' g ≫ p' q b' =
    pullback.snd q (base b' g) ≫ first g := testLift_snd _ _ _ _ _
@[reassoc] lemma secondLift_fst : secondLift q b b' g hg ≫ pullback.fst q b' =
    pullback.fst q (base b' g) := testLift_fst _ _ _ _ _
@[reassoc] lemma secondLift_snd : secondLift q b b' g hg ≫ p' q b' =
    pullback.snd q (base b' g) ≫ second g := testLift_snd _ _ _ _ _

@[expose] def inv : Test q b' g ⟶ Double (f q b b' g hg) :=
  pullback.lift (firstLift q b' g) (secondLift q b b' g hg) (by
    apply pullback.hom_ext
    · simp only [Category.assoc,totalMap_fst,firstLift_fst,secondLift_fst]
    · simp only [Category.assoc,totalMap_snd,firstLift_snd_assoc,secondLift_snd_assoc,
        edge_condition])
@[reassoc] lemma inv_first : inv q b b' g hg ≫ first (f q b b' g hg) = firstLift q b' g :=
  pullback.lift_fst _ _ _
@[reassoc] lemma inv_second : inv q b b' g hg ≫ second (f q b b' g hg) = secondLift q b b' g hg :=
  pullback.lift_snd _ _ _

@[reassoc] lemma inv_projection : inv q b b' g hg ≫ doubleProjection q b b' g hg =
    pullback.snd q (base b' g) := by
  apply pullback.hom_ext
  · simp only [Category.assoc,OriginalTestCechCoordinates318.double_first,
      inv_first_assoc,firstLift_snd]
  · simp only [Category.assoc,OriginalTestCechCoordinates318.double_second,
      inv_second_assoc,secondLift_snd]

/-- Exact full-test presentation of the original categorical double,
including both original total-space faces and its original base projection. -/
@[expose] def iso : Double (f q b b' g hg) ≅ Test q b' g where
  hom := hom q b b' g hg
  inv := inv q b b' g hg
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc,inv_first_assoc,firstLift_fst,hom_fst,Category.id_comp]
      · simp only [Category.assoc,inv_first_assoc,firstLift_snd,hom_snd_assoc,
          OriginalTestCechCoordinates318.double_first,Category.id_comp]
    · apply pullback.hom_ext
      · simp only [Category.assoc,inv_second_assoc,secondLift_fst,hom_fst,Category.id_comp,
          double_fst_equal]
      · simp only [Category.assoc,inv_second_assoc,secondLift_snd,hom_snd_assoc,
          OriginalTestCechCoordinates318.double_second,Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc,hom_fst,inv_first_assoc,firstLift_fst,Category.id_comp]
    · simp only [Category.assoc,hom_snd,inv_projection,Category.id_comp]

lemma iso_projection : (iso q b b' g hg).hom ≫ pullback.snd q (base b' g) =
    doubleProjection q b b' g hg := hom_snd q b b' g hg
end OriginalTestDoubleIso318
