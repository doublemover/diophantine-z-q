module
public import ActualAffineTripleMaps318
public section
noncomputable section
namespace ActualAffineTripleNerve318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AffineModuleBaseChange318
open AffineCechRings318 ActualAffineDoubleNerve318 ActualAffineTripleMaps318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S]

@[reassoc] lemma toTensor_pair01 : toTensor R S ≫ Spec.map (map12 R S) ≫ (doubleIso R S).inv =
    ActualOverlapDiagram318.pair01 (baseMap R S) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, inverse_first,
      spec_path _ _ _ (map12_left R S), toTensor_vertex0]
  · simp only [Category.assoc, inverse_second,
      spec_path _ _ _ (map12_right R S), toTensor_vertex1]

lemma toTensor_toActual : toTensor R S ≫ toActual R S = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, toActual_pair01, toTensor_pair01, Category.id_comp]
  · simp only [Category.assoc, toActual_pair12, toTensor_pair12_assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]

lemma toActual_toTensor : toActual R S ≫ toTensor R S = 𝟙 _ := by
  have h₀ : (outerIso R S).inv ≫ pullback.fst (baseMap R S)
      (Spec.map (CommRingCat.ofHom (algebraMap R (double R S))))=Spec.map (vertex1 R S) :=
    outer_inverse_first R S
  have h₁ : (outerIso R S).inv ≫ pullback.snd (baseMap R S)
      (Spec.map (CommRingCat.ofHom (algebraMap R (double R S))))=Spec.map (map23 R S) :=
    outer_inverse_second R S
  have hv₀ : (toActual R S ≫ toTensor R S) ≫ Spec.map (vertex1 R S)=Spec.map (vertex1 R S) := by
    calc
      _ = toActual R S ≫ (toTensor R S ≫ Spec.map (vertex1 R S)) := Category.assoc _ _ _
      _ = toActual R S ≫ ActualOverlapDiagram318.vertex0 (baseMap R S) :=
        congrArg (fun k => toActual R S ≫ k) (toTensor_vertex0 R S)
      _ = _ := toActual_vertex0 R S
  have hv₁ : (toActual R S ≫ toTensor R S) ≫ Spec.map (map23 R S)=Spec.map (map23 R S) := by
    calc
      _ = toActual R S ≫ (toTensor R S ≫ Spec.map (map23 R S)) := Category.assoc _ _ _
      _ = toActual R S ≫ (ActualOverlapDiagram318.pair12 (baseMap R S) ≫ (doubleIso R S).hom) :=
        congrArg (fun k => toActual R S ≫ k) (toTensor_pair12 R S)
      _ = (toActual R S ≫ ActualOverlapDiagram318.pair12 (baseMap R S)) ≫ (doubleIso R S).hom :=
        (Category.assoc _ _ _).symm
      _ = (Spec.map (map23 R S) ≫ (doubleIso R S).inv) ≫ (doubleIso R S).hom :=
        congrArg (fun k => k ≫ (doubleIso R S).hom) (toActual_pair12 R S)
      _ = _ := by simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  apply (cancel_mono (outerIso R S).inv).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc,Category.id_comp] using
      (congrArg (fun k => (toActual R S ≫ toTensor R S) ≫ k) h₀).trans (hv₀.trans h₀.symm)
  · simpa only [Category.assoc,Category.id_comp] using
      (congrArg (fun k => (toActual R S ≫ toTensor R S) ≫ k) h₁).trans (hv₁.trans h₁.symm)

/-- Explicit mutually inverse identification of the actual adjacent-double
scheme fiber-product triple with the original full triple tensor spectrum. -/
@[expose] def tripleIso : ActualOverlapDiagram318.Triple (baseMap R S) ≅ Spec (triple R S) where
  hom := toTensor R S
  inv := toActual R S
  hom_inv_id := toTensor_toActual R S
  inv_hom_id := toActual_toTensor R S

@[reassoc] lemma inverse_pair01 : (tripleIso R S).inv ≫
    ActualOverlapDiagram318.pair01 (baseMap R S) = Spec.map (map12 R S) ≫ (doubleIso R S).inv :=
  toActual_pair01 R S
@[reassoc] lemma inverse_pair12 : (tripleIso R S).inv ≫
    ActualOverlapDiagram318.pair12 (baseMap R S) = Spec.map (map23 R S) ≫ (doubleIso R S).inv :=
  toActual_pair12 R S

/-- The omitted pair map is the actual13 tensor map under the same two
comparison isomorphisms; both outer projections are checked. -/
@[reassoc] lemma inverse_pair02 : (tripleIso R S).inv ≫
    ActualOverlapDiagram318.pair02 (baseMap R S) = Spec.map (map13 R S) ≫ (doubleIso R S).inv := by
  apply pullback.hom_ext
  · simp only [Category.assoc, ActualOverlapDiagram318.pair02_first,
      inverse_first, spec_path _ _ _ (map13_left R S)]
    exact toActual_vertex0 R S
  · simp only [Category.assoc, ActualOverlapDiagram318.pair02_second,
      inverse_second, spec_path _ _ _ (map13_right R S)]
    exact toActual_vertex2 R S

/-- All three named pair maps of the actual scheme Cech nerve are preserved
simultaneously, rather than only the isomorphism type of its triple object. -/
lemma all_pairs :
    (tripleIso R S).inv ≫ ActualOverlapDiagram318.pair01 (baseMap R S) =
        Spec.map (map12 R S) ≫ (doubleIso R S).inv ∧
    (tripleIso R S).inv ≫ ActualOverlapDiagram318.pair12 (baseMap R S) =
        Spec.map (map23 R S) ≫ (doubleIso R S).inv ∧
    (tripleIso R S).inv ≫ ActualOverlapDiagram318.pair02 (baseMap R S) =
        Spec.map (map13 R S) ≫ (doubleIso R S).inv :=
  ⟨inverse_pair01 R S, inverse_pair12 R S, inverse_pair02 R S⟩
end ActualAffineTripleNerve318
