module
public import ActualOriginalGraphMassNormalization318
public section
noncomputable section
namespace ActualOriginalNormalLevelChart318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318
set_option maxHeartbeats 16000000

@[expose] def LevelParameters := ℝ×Parameters
@[expose] def levelRadicand (κ : ℝ) (z : LevelParameters) : ℝ := radicand κ z.2+z.1
@[expose] def levelGraph (κ : ℝ) (z : LevelParameters) : Coordinates ℝ :=
  ((Real.sqrt (levelRadicand κ z),z.2.1),z.2.2.1,z.2.2.2)
@[expose] def normalCoordinates (κ : ℝ) (x : Coordinates ℝ) : LevelParameters :=
  (equation κ x,projection x)
lemma levelRadicand_continuous (κ : ℝ) : Continuous (levelRadicand κ) := by
  unfold levelRadicand
  exact ((radicand_continuous κ).comp continuous_snd).add continuous_fst
lemma levelGraph_continuous (κ : ℝ) : Continuous (levelGraph κ) := by
  unfold levelGraph
  fun_prop
lemma normalCoordinates_continuous (κ : ℝ) : Continuous (normalCoordinates κ) := by
  unfold normalCoordinates
  exact (ActualOriginalRealGoodRegion318.original_equation_continuous κ).prodMk projection_continuous
lemma actual_level_equation (κ : ℝ) (z : LevelParameters) (hz : 0≤levelRadicand κ z) :
    equation κ (levelGraph κ z)=z.1 := by
  have hs := Real.sq_sqrt hz
  dsimp [levelGraph,levelRadicand,radicand,equation] at *
  nlinarith
lemma original_normal_radicand (κ : ℝ) (x : Coordinates ℝ) :
    levelRadicand κ (normalCoordinates κ x)=x.1.1^2 := by
  dsimp [levelRadicand,normalCoordinates,radicand,projection,equation]
  ring
lemma original_normal_inverse (κ : ℝ) (x : Coordinates ℝ) (hx : 0≤x.1.1) :
    levelGraph κ (normalCoordinates κ x)=x := by
  have hs : Real.sqrt (levelRadicand κ (normalCoordinates κ x))=x.1.1 := by
    rw [original_normal_radicand,Real.sqrt_sq hx]
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩,w⟩
  change ((Real.sqrt (levelRadicand κ (normalCoordinates κ ((a,b),(c,d),w))),b),(c,d),w)=_
  rw [hs]
lemma normal_level_inverse (κ : ℝ) (z : LevelParameters) (hz : 0≤levelRadicand κ z) :
    normalCoordinates κ (levelGraph κ z)=z := by
  apply Prod.ext
  · exact actual_level_equation κ z hz
  · rfl
@[expose] def actualNormalChart (κ : ℝ) :
    {z : LevelParameters // 0<levelRadicand κ z} ≃ {x : Coordinates ℝ // 0<x.1.1} where
  toFun z := ⟨levelGraph κ z.1,Real.sqrt_pos.2 z.2⟩
  invFun x := ⟨normalCoordinates κ x.1,by
    rw [original_normal_radicand]
    exact sq_pos_of_pos x.2⟩
  left_inv z := Subtype.ext (normal_level_inverse κ z.1 z.2.le)
  right_inv x := Subtype.ext (original_normal_inverse κ x.1 x.2.le)
lemma level_zero_graph (κ : ℝ) (v : Parameters) : levelGraph κ (0,v)=graph κ v := by
  simp only [levelGraph,levelRadicand,zero_add,add_zero,graph]

end ActualOriginalNormalLevelChart318
