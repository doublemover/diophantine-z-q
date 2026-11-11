module
public import OriginalSchemeIsoEvaluation318
public section
noncomputable section
namespace OriginalTestTripleIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassBaseChange318 ActualOverlapDiagram318 OriginalTestCechCoordinates318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T T' : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (b' : T' ⟶ B)
  (g : T' ⟶ T) (hg : g ≫ b = b')
abbrev base := vertex0 g ≫ b'
abbrev Test := pullback q (base b' g)

lemma vertex01_base : vertex0 g ≫ g = vertex1 g ≫ g := by
  simp only [vertex0,vertex1,Category.assoc,edge_condition]
lemma vertex12_base : vertex1 g ≫ g = vertex2 g ≫ g := by
  change (pair01 g ≫ second g) ≫ g = (pair12 g ≫ second g) ≫ g
  rw [middle_condition,Category.assoc,Category.assoc,edge_condition]
lemma vertex02_base : vertex0 g ≫ g = vertex2 g ≫ g :=
  (vertex01_base g).trans (vertex12_base g)

@[expose] def hom : Triple (f q b b' g hg) ⟶ Test q b' g :=
  pullback.lift (vertex0 (f q b b' g hg) ≫ pullback.fst q b')
    (tripleProjection q b b' g hg) (by
      calc
        _ = (vertex0 (f q b b' g hg) ≫ p' q b') ≫ b' := by
          simpa only [Category.assoc] using congrArg
            (fun a => vertex0 (f q b b' g hg) ≫ a) (pullback.condition (f:=q) (g:=b'))
        _ = (tripleProjection q b b' g hg ≫ vertex0 g) ≫ b' :=
          congrArg (fun a => a ≫ b') (OriginalTestCechCoordinates318.triple_vertex0 q b b' g hg).symm
        _ = _ := Category.assoc _ _ _)
@[reassoc] lemma hom_fst : hom q b b' g hg ≫ pullback.fst q (base b' g) =
    vertex0 (f q b b' g hg) ≫ pullback.fst q b' := pullback.lift_fst _ _ _
@[reassoc] lemma hom_snd : hom q b b' g hg ≫ pullback.snd q (base b' g) =
    tripleProjection q b b' g hg := pullback.lift_snd _ _ _

@[expose] def lift0 : Test q b' g ⟶ pullback q b' :=
  testLift q b' (pullback.fst q (base b' g)) (pullback.snd q (base b' g) ≫ vertex0 g)
    (by simpa only [Category.assoc] using (pullback.condition (f:=q) (g:=base b' g)))
@[expose] def lift1 : Test q b' g ⟶ pullback q b' :=
  testLift q b' (pullback.fst q (base b' g)) (pullback.snd q (base b' g) ≫ vertex1 g)
    (by
      have he := base_equal b b' g hg (vertex0 g) (vertex1 g) (vertex01_base g)
      simpa only [Category.assoc,he] using (pullback.condition (f:=q) (g:=base b' g)))
@[expose] def lift2 : Test q b' g ⟶ pullback q b' :=
  testLift q b' (pullback.fst q (base b' g)) (pullback.snd q (base b' g) ≫ vertex2 g)
    (by
      have he := base_equal b b' g hg (vertex0 g) (vertex2 g) (vertex02_base g)
      simpa only [Category.assoc,he] using (pullback.condition (f:=q) (g:=base b' g)))
@[reassoc] lemma lift0_fst : lift0 q b' g ≫ pullback.fst q b' =
    pullback.fst q (base b' g) := testLift_fst _ _ _ _ _
@[reassoc] lemma lift0_snd : lift0 q b' g ≫ p' q b' =
    pullback.snd q (base b' g) ≫ vertex0 g := testLift_snd _ _ _ _ _
@[reassoc] lemma lift1_fst : lift1 q b b' g hg ≫ pullback.fst q b' =
    pullback.fst q (base b' g) := testLift_fst _ _ _ _ _
@[reassoc] lemma lift1_snd : lift1 q b b' g hg ≫ p' q b' =
    pullback.snd q (base b' g) ≫ vertex1 g := testLift_snd _ _ _ _ _
@[reassoc] lemma lift2_fst : lift2 q b b' g hg ≫ pullback.fst q b' =
    pullback.fst q (base b' g) := testLift_fst _ _ _ _ _
@[reassoc] lemma lift2_snd : lift2 q b b' g hg ≫ p' q b' =
    pullback.snd q (base b' g) ≫ vertex2 g := testLift_snd _ _ _ _ _

@[expose] def pair01Lift : Test q b' g ⟶ Double (f q b b' g hg) :=
  pullback.lift (lift0 q b' g) (lift1 q b b' g hg) (by
    apply pullback.hom_ext
    · simp only [Category.assoc,totalMap_fst,lift0_fst,lift1_fst]
    · simp only [Category.assoc,totalMap_snd,lift0_snd_assoc,lift1_snd_assoc,vertex01_base])
@[expose] def pair12Lift : Test q b' g ⟶ Double (f q b b' g hg) :=
  pullback.lift (lift1 q b b' g hg) (lift2 q b b' g hg) (by
    apply pullback.hom_ext
    · simp only [Category.assoc,totalMap_fst,lift1_fst,lift2_fst]
    · simp only [Category.assoc,totalMap_snd,lift1_snd_assoc,lift2_snd_assoc,vertex12_base])

@[expose] def inv : Test q b' g ⟶ Triple (f q b b' g hg) :=
  pullback.lift (pair01Lift q b b' g hg) (pair12Lift q b b' g hg) (by
    simp only [pair01Lift,pair12Lift,pullback.lift_fst,pullback.lift_snd])
@[reassoc] lemma inv_vertex0 : inv q b b' g hg ≫ vertex0 (f q b b' g hg) = lift0 q b' g := by
  simp only [inv,vertex0,pair01Lift,Category.assoc,pullback.lift_fst_assoc,pullback.lift_fst]
@[reassoc] lemma inv_vertex1 : inv q b b' g hg ≫ vertex1 (f q b b' g hg) = lift1 q b b' g hg := by
  simp only [inv,vertex1,pair01Lift,Category.assoc,pullback.lift_fst_assoc,pullback.lift_snd]
@[reassoc] lemma inv_vertex2 : inv q b b' g hg ≫ vertex2 (f q b b' g hg) = lift2 q b b' g hg := by
  simp only [inv,vertex2,pair12Lift,Category.assoc,pullback.lift_snd_assoc,pullback.lift_snd]

@[reassoc] lemma inv_projection : inv q b b' g hg ≫ tripleProjection q b b' g hg =
    pullback.snd q (base b' g) := by
  apply triple_hom_ext g
  · simp only [Category.assoc,OriginalTestCechCoordinates318.triple_vertex0,inv_vertex0_assoc,lift0_snd]
  · simp only [Category.assoc,OriginalTestCechCoordinates318.triple_vertex1,inv_vertex1_assoc,lift1_snd]
  · simp only [Category.assoc,OriginalTestCechCoordinates318.triple_vertex2,inv_vertex2_assoc,lift2_snd]

/-- The full original categorical triple is the full original family test
on the actual base triple. All three original vertices are retained. -/
@[expose] def iso : Triple (f q b b' g hg) ≅ Test q b' g where
  hom := hom q b b' g hg
  inv := inv q b b' g hg
  hom_inv_id := by
    apply triple_hom_ext (f q b b' g hg)
    · apply pullback.hom_ext
      · simp only [Category.assoc,inv_vertex0_assoc,lift0_fst,hom_fst,Category.id_comp]
      · simp only [Category.assoc,inv_vertex0_assoc,lift0_snd,hom_snd_assoc,
          OriginalTestCechCoordinates318.triple_vertex0,Category.id_comp]
    · apply pullback.hom_ext
      · simp only [Category.assoc,inv_vertex1_assoc,lift1_fst,hom_fst,Category.id_comp,triple_fst01]
      · simp only [Category.assoc,inv_vertex1_assoc,lift1_snd,hom_snd_assoc,
          OriginalTestCechCoordinates318.triple_vertex1,Category.id_comp]
    · apply pullback.hom_ext
      · simp only [Category.assoc,inv_vertex2_assoc,lift2_fst,hom_fst,Category.id_comp,triple_fst01,triple_fst12]
      · simp only [Category.assoc,inv_vertex2_assoc,lift2_snd,hom_snd_assoc,
          OriginalTestCechCoordinates318.triple_vertex2,Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc,hom_fst,inv_vertex0_assoc,lift0_fst,Category.id_comp]
    · simp only [Category.assoc,hom_snd,inv_projection,Category.id_comp]

lemma iso_projection : (iso q b b' g hg).hom ≫ pullback.snd q (base b' g) =
    tripleProjection q b b' g hg := hom_snd q b b' g hg
end OriginalTestTripleIso318
