module
public import RelativeCechClassSeparated318
public section
noncomputable section
namespace OriginalTestCechCoordinates318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassBaseChange318 ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T T' : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (b' : T' ⟶ B)
  (g : T' ⟶ T) (hg : g ≫ b = b')
abbrev f := totalMap q b b' g hg
abbrev p := pullback.snd q b
abbrev p' := pullback.snd q b'

@[expose] def doubleProjection : Double (f q b b' g hg) ⟶ Double g :=
  doubleMap g (f q b b' g hg) (p' q b') (p q b) (totalMap_snd q b b' g hg).symm
@[expose] def tripleProjection : Triple (f q b b' g hg) ⟶ Triple g :=
  tripleMap g (f q b b' g hg) (p' q b') (p q b) (totalMap_snd q b b' g hg).symm

@[reassoc] lemma double_first : doubleProjection q b b' g hg ≫ first g =
    first (f q b b' g hg) ≫ p' q b' :=
  ActualDescentBaseChangeDiagram318.double_first _ _ _ _ _
@[reassoc] lemma double_second : doubleProjection q b b' g hg ≫ second g =
    second (f q b b' g hg) ≫ p' q b' :=
  ActualDescentBaseChangeDiagram318.double_second _ _ _ _ _
@[reassoc] lemma triple_vertex0 : tripleProjection q b b' g hg ≫ vertex0 g =
    vertex0 (f q b b' g hg) ≫ p' q b' :=
  ActualDescentBaseChangeDiagram318.triple_vertex0 _ _ _ _ _
@[reassoc] lemma triple_vertex1 : tripleProjection q b b' g hg ≫ vertex1 g =
    vertex1 (f q b b' g hg) ≫ p' q b' :=
  ActualDescentBaseChangeDiagram318.triple_vertex1 _ _ _ _ _
@[reassoc] lemma triple_vertex2 : tripleProjection q b b' g hg ≫ vertex2 g =
    vertex2 (f q b b' g hg) ≫ p' q b' :=
  ActualDescentBaseChangeDiagram318.triple_vertex2 _ _ _ _ _

lemma double_fst_equal : first (f q b b' g hg) ≫ pullback.fst q b' =
    second (f q b b' g hg) ≫ pullback.fst q b' := by
  have h := congrArg (fun a => a ≫ pullback.fst q b) (edge_condition (f q b b' g hg))
  simpa only [Category.assoc,totalMap_fst] using h

lemma triple_fst01 : vertex0 (f q b b' g hg) ≫ pullback.fst q b' =
    vertex1 (f q b b' g hg) ≫ pullback.fst q b' := by
  change (pair01 (f q b b' g hg) ≫ first (f q b b' g hg)) ≫ _ =
    (pair01 (f q b b' g hg) ≫ second (f q b b' g hg)) ≫ _
  rw [Category.assoc,Category.assoc,double_fst_equal]
lemma triple_fst12 : vertex1 (f q b b' g hg) ≫ pullback.fst q b' =
    vertex2 (f q b b' g hg) ≫ pullback.fst q b' := by
  change (pair01 (f q b b' g hg) ≫ second (f q b b' g hg)) ≫ _ =
    (pair12 (f q b b' g hg) ≫ second (f q b b' g hg)) ≫ _
  rw [middle_condition,Category.assoc,Category.assoc,double_fst_equal]

/-- The actual triple is determined by its three original vertex maps. -/
lemma triple_hom_ext {Z : Scheme.{u}} {a c : Z ⟶ Triple g}
    (h₀ : a ≫ vertex0 g = c ≫ vertex0 g)
    (h₁ : a ≫ vertex1 g = c ≫ vertex1 g)
    (h₂ : a ≫ vertex2 g = c ≫ vertex2 g) : a = c := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans (h₀.trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans (h₁.trans (Category.assoc _ _ _).symm)
  · apply pullback.hom_ext
    · simpa only [vertex1,Category.assoc,← middle_condition] using h₁
    · exact (Category.assoc _ _ _).trans (h₂.trans (Category.assoc _ _ _).symm)

lemma base_equal {Z : Scheme.{u}} (k l : Z ⟶ T') (h : k ≫ g = l ≫ g) :
    k ≫ b' = l ≫ b' := by
  rw [← hg,← Category.assoc,← Category.assoc,h]

/-- Exact original fiber-product point with named total and base maps. -/
@[expose] def testLift {Z : Scheme.{u}} (z : Z ⟶ C) (k : Z ⟶ T')
    (h : z ≫ q = k ≫ b') : Z ⟶ pullback q b' := pullback.lift z k h
@[reassoc] lemma testLift_fst {Z : Scheme.{u}} (z : Z ⟶ C) (k : Z ⟶ T')
    (h : z ≫ q = k ≫ b') : testLift q b' z k h ≫ pullback.fst q b' = z :=
  pullback.lift_fst _ _ _
@[reassoc] lemma testLift_snd {Z : Scheme.{u}} (z : Z ⟶ C) (k : Z ⟶ T')
    (h : z ≫ q = k ≫ b') : testLift q b' z k h ≫ p' q b' = k :=
  pullback.lift_snd _ _ _

lemma testLift_total {Z : Scheme.{u}} (z : Z ⟶ C) (k l : Z ⟶ T')
    (hk : z ≫ q = k ≫ b') (hl : z ≫ q = l ≫ b') (h : k ≫ g = l ≫ g) :
    testLift q b' z k hk ≫ f q b b' g hg = testLift q b' z l hl ≫ f q b b' g hg := by
  apply pullback.hom_ext
  · simp only [Category.assoc,totalMap_fst,testLift_fst]
  · simpa only [Category.assoc,totalMap_snd,testLift_snd_assoc] using h
end OriginalTestCechCoordinates318
