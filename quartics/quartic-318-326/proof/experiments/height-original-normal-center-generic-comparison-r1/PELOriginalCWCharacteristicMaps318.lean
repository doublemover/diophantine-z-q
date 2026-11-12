module
public import StandardCellCoordinates318
public import CharacteristicPartialEquiv318
public import PELOriginalDiskAttachingStrata318
public import PELOriginalEdgeCharacteristic318
public section
noncomputable section
namespace PELOriginalCWCharacteristicMaps318
open Set Metric
open PELUnlevelledComplexBase318 PELOriginalVertexStratum318 PELOriginalEdgeStrata318
open PELOriginalDiskAttachingStrata318

@[expose] def vertex (i : Fin 5) : UnlevelledBase := (vertexEnumeration i).val
@[expose] def edge (i : Fin 14) : Set UnlevelledBase := EdgeImage (edgeRepresentative i)

@[expose] def zeroChar (i : Fin 5) : closedBall (0:Fin 0 → ℝ) 1 → UnlevelledBase :=
  fun _ => vertex i

@[expose] def zeroHomeomorph (i : Fin 5) : ball (0:Fin 0 → ℝ) 1 ≃ₜ ({vertex i}:Set UnlevelledBase) where
  toFun _ := ⟨vertex i,rfl⟩
  invFun _ := ⟨0,by simp⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv y := by apply Subtype.ext; exact y.property.symm
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

@[expose] def vertexMap (i : Fin 5) : PartialEquiv (Fin 0 → ℝ) UnlevelledBase :=
  CharacteristicPartialEquiv318.cellMap (zeroChar i) {vertex i} (zeroHomeomorph i) (fun _ => rfl)

@[expose] def edgeChar (i : Fin 14) : closedBall (0:Fin 1 → ℝ) 1 → UnlevelledBase :=
  PELOriginalEdgeCharacteristic318.characteristic (edgeRepresentative i) ∘ StandardCellCoordinates318.oneClosed

@[expose] def edgeHomeomorph (i : Fin 14) : ball (0:Fin 1 → ℝ) 1 ≃ₜ edge i :=
  StandardCellCoordinates318.oneOpen.trans (PELOriginalEdgeCharacteristic318.originalOpenEdge (edgeRepresentative i))

@[expose] def edgeMap (i : Fin 14) : PartialEquiv (Fin 1 → ℝ) UnlevelledBase :=
  CharacteristicPartialEquiv318.cellMap (edgeChar i) (edge i) (edgeHomeomorph i) (fun _ => rfl)

@[expose] def faceChar : closedBall (0:Fin 2 → ℝ) 1 → UnlevelledBase :=
  PELOriginalDiskCharacteristic318.characteristic ∘ StandardCellCoordinates318.twoClosed

@[expose] def faceHomeomorph : ball (0:Fin 2 → ℝ) 1 ≃ₜ PELOriginalDiskCharacteristic318.openCell :=
  StandardCellCoordinates318.twoOpen.trans PELOriginalOpenTwoCell318.originalOpenTwoCell

@[expose] def faceMap : PartialEquiv (Fin 2 → ℝ) UnlevelledBase :=
  CharacteristicPartialEquiv318.cellMap faceChar PELOriginalDiskCharacteristic318.openCell faceHomeomorph (fun _ => rfl)

theorem vertex_open (i : Fin 5) : vertexMap i '' ball 0 1={vertex i} := CharacteristicPartialEquiv318.open_image ..
theorem edge_open (i : Fin 14) : edgeMap i '' ball 0 1=edge i := CharacteristicPartialEquiv318.open_image ..
theorem face_open : faceMap '' ball 0 1=PELOriginalDiskCharacteristic318.openCell := CharacteristicPartialEquiv318.open_image ..

theorem vertex_closed (i : Fin 5) : vertexMap i '' closedBall 0 1={vertex i} := by
  rw [show vertexMap i '' closedBall 0 1=Set.range (zeroChar i) from CharacteristicPartialEquiv318.closed_image ..]
  ext q
  constructor
  · rintro ⟨z,rfl⟩; rfl
  · intro hq
    exact ⟨⟨0,by simp⟩,hq.symm⟩

theorem edge_range (i : Fin 14) : Set.range (edgeChar i)=Set.range (PELOriginalEdgeCharacteristic318.characteristic (edgeRepresentative i)) := by
  ext q
  constructor
  · rintro ⟨z,rfl⟩; exact ⟨StandardCellCoordinates318.oneClosed z,rfl⟩
  · rintro ⟨z,rfl⟩; exact ⟨StandardCellCoordinates318.oneClosed.symm z,by simp [edgeChar]⟩

theorem edge_closed (i : Fin 14) : edgeMap i '' closedBall 0 1=
    edge i ∪ {projection (PELOriginalActualVertexGluing318.vertexPoint
      (PELDirichletSidePairingData318.start (edgeRepresentative i))).val,
      projection (PELOriginalActualVertexGluing318.vertexPoint
      (PELDirichletSidePairingData318.finish (edgeRepresentative i))).val} := by
  rw [show edgeMap i '' closedBall 0 1=Set.range (edgeChar i) from CharacteristicPartialEquiv318.closed_image ..,
    edge_range,PELOriginalEdgeCharacteristic318.characteristic_range]
  rfl

theorem face_closed : faceMap '' closedBall 0 1=Set.univ := by
  rw [show faceMap '' closedBall 0 1=Set.range faceChar from CharacteristicPartialEquiv318.closed_image ..]
  exact Set.range_eq_univ.mpr (PELOriginalDiskCharacteristic318.characteristic_surjective.comp StandardCellCoordinates318.twoClosed.surjective)

theorem vertex_continuous (i : Fin 5) : ContinuousOn (vertexMap i) (closedBall 0 1) :=
  CharacteristicPartialEquiv318.continuousOn_closed _ continuous_const _ _ _
theorem edge_continuous (i : Fin 14) : ContinuousOn (edgeMap i) (closedBall 0 1) :=
  CharacteristicPartialEquiv318.continuousOn_closed _ ((PELOriginalEdgeCharacteristic318.characteristic_continuous _).comp StandardCellCoordinates318.oneClosed.continuous) _ _ _
theorem face_continuous : ContinuousOn faceMap (closedBall 0 1) :=
  CharacteristicPartialEquiv318.continuousOn_closed _ (PELOriginalDiskCharacteristic318.characteristic_continuous.comp StandardCellCoordinates318.twoClosed.continuous) _ _ _

theorem vertex_boundary (i : Fin 5) (z : Fin 0 → ℝ) (hz : z∈sphere 0 1) : False := by
  have h : z=0 := Subsingleton.elim _ _
  simpa [h] using hz

theorem edge_boundary (i : Fin 14) (z : Fin 1 → ℝ) (hz : z∈sphere 0 1) :
    edgeMap i z∈VertexImage := by
  have hzc : z∈closedBall 0 1 := le_of_eq hz
  rw [show edgeMap i z=edgeChar i ⟨z,hzc⟩ from CharacteristicPartialEquiv318.on_closed _ _ _ _ ⟨z,hzc⟩]
  exact PELOriginalEdgeCharacteristic318.boundary_vertex (edgeRepresentative i) (StandardCellCoordinates318.oneClosed ⟨z,hzc⟩) (StandardCellCoordinates318.one_sphere z hz)

theorem face_boundary (z : Fin 2 → ℝ) (hz : z∈sphere 0 1) : faceMap z∈PELOriginalDiskCharacteristic318.attachingImage := by
  have hzc : z∈closedBall 0 1 := le_of_eq hz
  rw [show faceMap z=faceChar ⟨z,hzc⟩ from CharacteristicPartialEquiv318.on_closed _ _ _ _ ⟨z,hzc⟩]
  exact ⟨StandardCellCoordinates318.twoClosed ⟨z,hzc⟩,(StandardCellCoordinates318.two_sphere z).mp hz,rfl⟩

theorem vertex_cover (q : UnlevelledBase) (hq : q∈VertexImage) :
    ∃ i : Fin 5, q∈vertexMap i '' closedBall 0 1 := by
  obtain ⟨i,hi⟩ := vertexEnumeration.surjective ⟨q,hq⟩
  refine ⟨i,?_⟩
  rw [vertex_closed]
  exact (congrArg Subtype.val hi).symm

theorem edge_cover (e : Fin 28) (q : UnlevelledBase) (hq : q∈EdgeImage e) :
    ∃ i : Fin 14, q∈edgeMap i '' closedBall 0 1 := by
  have he : EdgeImage (edgeRepresentative (edgeClass e))=EdgeImage e :=
    (edgeImage_eq_iff _ _).mpr (edgeRepresentative_class _)
  refine ⟨edgeClass e,?_⟩
  rw [edge_closed]
  exact Or.inl (he.symm ▸ hq)

theorem vertex_injective : Function.Injective vertex := by
  intro i j h
  exact vertexEnumeration.injective (Subtype.ext h)

theorem face_vertex_disjoint (i : Fin 5) : Disjoint PELOriginalDiskCharacteristic318.openCell {vertex i} := by
  apply Set.disjoint_left.mpr
  intro q hq hv
  have hv' : q∈VertexImage := by
    change q=vertex i at hv
    rw [hv]
    exact (vertexEnumeration i).property
  have ha : q∈PELOriginalDiskCharacteristic318.attachingImage := by rw [attaching_exact_lower_strata]; exact Or.inl hv'
  exact Set.disjoint_left.mp PELOriginalDiskCharacteristic318.open_attaching_disjoint hq ha

theorem face_edge_disjoint (i : Fin 14) : Disjoint PELOriginalDiskCharacteristic318.openCell (edge i) := by
  apply Set.disjoint_left.mpr
  intro q hq he
  have ha : q∈PELOriginalDiskCharacteristic318.attachingImage := by
    rw [attaching_exact_lower_strata]
    exact Or.inr (Set.mem_iUnion.mpr ⟨edgeRepresentative i,he⟩)
  exact Set.disjoint_left.mp PELOriginalDiskCharacteristic318.open_attaching_disjoint hq ha
end PELOriginalCWCharacteristicMaps318
