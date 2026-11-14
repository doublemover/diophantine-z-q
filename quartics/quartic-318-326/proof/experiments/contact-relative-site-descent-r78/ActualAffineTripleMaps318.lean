module
public import ActualAffineDoubleNerve318
public section
noncomputable section
namespace ActualAffineTripleMaps318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AffineModuleBaseChange318
open AffineCechRings318 ActualAffineDoubleNerve318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S]

/-- Actual map into the adjacent-double fiber-product triple. Its two
components are the original12 and23 tensor-spectrum maps. -/
@[expose] def toActual : Spec (triple R S) ⟶ ActualOverlapDiagram318.Triple (baseMap R S) :=
  pullback.lift (Spec.map (map12 R S) ≫ (doubleIso R S).inv)
    (Spec.map (map23 R S) ≫ (doubleIso R S).inv) (by
      rw [Category.assoc, inverse_second, Category.assoc, inverse_first,
        spec_path _ _ _ (map12_right R S), spec_path _ _ _ (map23_left R S)])

@[reassoc] lemma toActual_pair01 : toActual R S ≫
    ActualOverlapDiagram318.pair01 (baseMap R S) = Spec.map (map12 R S) ≫ (doubleIso R S).inv :=
  pullback.lift_fst _ _ _
@[reassoc] lemma toActual_pair12 : toActual R S ≫
    ActualOverlapDiagram318.pair12 (baseMap R S) = Spec.map (map23 R S) ≫ (doubleIso R S).inv :=
  pullback.lift_snd _ _ _
@[reassoc] lemma toActual_vertex0 : toActual R S ≫
    ActualOverlapDiagram318.vertex0 (baseMap R S) = Spec.map (vertex1 R S) := by
  rw [ActualOverlapDiagram318.vertex0, ← Category.assoc, toActual_pair01,
    Category.assoc, inverse_first, spec_path _ _ _ (map12_left R S)]
@[reassoc] lemma toActual_vertex1 : toActual R S ≫
    ActualOverlapDiagram318.vertex1 (baseMap R S) = Spec.map (vertex2 R S) := by
  rw [ActualOverlapDiagram318.vertex1, ← Category.assoc, toActual_pair01,
    Category.assoc, inverse_second, spec_path _ _ _ (map12_right R S)]
@[reassoc] lemma toActual_vertex2 : toActual R S ≫
    ActualOverlapDiagram318.vertex2 (baseMap R S) = Spec.map (vertex3 R S) := by
  rw [ActualOverlapDiagram318.vertex2, ← Category.assoc, toActual_pair12,
    Category.assoc, inverse_second, spec_path _ _ _ (map23_right R S)]

/-- The other parenthesization of the triple fiber product is the literal
S tensor_R (S tensor_R S) spectrum through its actual limit comparison. -/
@[expose] def outerIso : pullback (baseMap R S)
    (Spec.map (CommRingCat.ofHom (algebraMap R (double R S)))) ≅ Spec (triple R S) :=
  pullbackSpecIso R S (double R S)

@[reassoc] lemma outer_inverse_first : (outerIso R S).inv ≫ pullback.fst _ _ =
    Spec.map (vertex1 R S) := pullbackSpecIso_inv_fst' R S (double R S)
@[reassoc] lemma outer_inverse_second : (outerIso R S).inv ≫ pullback.snd _ _ =
    Spec.map (map23 R S) := pullbackSpecIso_inv_snd R S (double R S)
@[reassoc] lemma outer_forward_first : (outerIso R S).hom ≫ Spec.map (vertex1 R S) =
    pullback.fst _ _ := pullbackSpecIso_hom_fst' R S (double R S)
@[reassoc] lemma outer_forward_second : (outerIso R S).hom ≫ Spec.map (map23 R S) =
    pullback.snd _ _ := pullbackSpecIso_hom_snd R S (double R S)

/-- Explicit inverse candidate, built from vertex0 and pair12 of the
actual triple, not from an assumed affine comparison. -/
@[expose] def toTensor : ActualOverlapDiagram318.Triple (baseMap R S) ⟶ Spec (triple R S) :=
  pullback.lift (ActualOverlapDiagram318.vertex0 (baseMap R S))
    (ActualOverlapDiagram318.pair12 (baseMap R S) ≫ (doubleIso R S).hom) (by
      change (ActualOverlapDiagram318.pair01 (baseMap R S) ≫
        ActualOverlapDiagram318.first (baseMap R S)) ≫ baseMap R S = _
      calc
        _ = ActualOverlapDiagram318.pair01 (baseMap R S) ≫
            (ActualOverlapDiagram318.first (baseMap R S) ≫ baseMap R S) := Category.assoc _ _ _
        _ = ActualOverlapDiagram318.pair01 (baseMap R S) ≫
            (ActualOverlapDiagram318.second (baseMap R S) ≫ baseMap R S) :=
          congrArg (fun k => ActualOverlapDiagram318.pair01 (baseMap R S) ≫ k)
            (ActualOverlapDiagram318.edge_condition (baseMap R S))
        _ = (ActualOverlapDiagram318.pair01 (baseMap R S) ≫
            ActualOverlapDiagram318.second (baseMap R S)) ≫ baseMap R S := (Category.assoc _ _ _).symm
        _ = (ActualOverlapDiagram318.pair12 (baseMap R S) ≫
            ActualOverlapDiagram318.first (baseMap R S)) ≫ baseMap R S :=
          congrArg (fun k => k ≫ baseMap R S) (ActualOverlapDiagram318.middle_condition (baseMap R S))
        _ = ActualOverlapDiagram318.pair12 (baseMap R S) ≫
            (ActualOverlapDiagram318.first (baseMap R S) ≫ baseMap R S) := Category.assoc _ _ _
        _ = ActualOverlapDiagram318.pair12 (baseMap R S) ≫
            ((doubleIso R S).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (double R S)))) :=
          congrArg (fun k => ActualOverlapDiagram318.pair12 (baseMap R S) ≫ k) (forward_base R S).symm
        _ = _ := (Category.assoc _ _ _).symm) ≫ (outerIso R S).hom

@[reassoc] lemma toTensor_vertex0 : toTensor R S ≫ Spec.map (vertex1 R S) =
    ActualOverlapDiagram318.vertex0 (baseMap R S) := by
  rw [toTensor, Category.assoc, outer_forward_first, pullback.lift_fst]
@[reassoc] lemma toTensor_pair12 : toTensor R S ≫ Spec.map (map23 R S) =
    ActualOverlapDiagram318.pair12 (baseMap R S) ≫ (doubleIso R S).hom := by
  rw [toTensor, Category.assoc, outer_forward_second, pullback.lift_snd]
@[reassoc] lemma toTensor_vertex1 : toTensor R S ≫ Spec.map (vertex2 R S) =
    ActualOverlapDiagram318.vertex1 (baseMap R S) := by
  rw [← spec_path _ _ _ (map23_left R S), ← Category.assoc, toTensor_pair12,
    Category.assoc, forward_first]
  exact (ActualOverlapDiagram318.middle_condition (baseMap R S)).symm
@[reassoc] lemma toTensor_vertex2 : toTensor R S ≫ Spec.map (vertex3 R S) =
    ActualOverlapDiagram318.vertex2 (baseMap R S) := by
  rw [← spec_path _ _ _ (map23_right R S), ← Category.assoc, toTensor_pair12,
    Category.assoc, forward_second]

end ActualAffineTripleMaps318
