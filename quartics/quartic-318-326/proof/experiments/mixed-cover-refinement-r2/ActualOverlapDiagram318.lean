module
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace ActualOverlapDiagram318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {U T B : Scheme.{u}} (f : U ⟶ T)

/-- The actual double overlap of a map, before any covering hypothesis. -/
abbrev Double := pullback f f
abbrev first : Double f ⟶ U := pullback.fst f f
abbrev second : Double f ⟶ U := pullback.snd f f

lemma edge_condition : first f ≫ f = second f ≫ f := pullback.condition

/-- The actual triple overlap as two adjacent double overlaps. -/
abbrev Triple := pullback (second f) (first f)
abbrev pair01 : Triple f ⟶ Double f := pullback.fst (second f) (first f)
abbrev pair12 : Triple f ⟶ Double f := pullback.snd (second f) (first f)
abbrev vertex0 : Triple f ⟶ U := pair01 f ≫ first f
abbrev vertex1 : Triple f ⟶ U := pair01 f ≫ second f
abbrev vertex2 : Triple f ⟶ U := pair12 f ≫ second f

lemma middle_condition : pair01 f ≫ second f = pair12 f ≫ first f := pullback.condition

lemma outer_condition : vertex0 f ≫ f = vertex2 f ≫ f := by
  calc
    vertex0 f ≫ f = pair01 f ≫ second f ≫ f := by
      rw [vertex0, Category.assoc, edge_condition]
    _ = pair12 f ≫ first f ≫ f := by
      rw [← Category.assoc, middle_condition, Category.assoc]
    _ = vertex2 f ≫ f := by rw [edge_condition, vertex2, Category.assoc]

/-- The omitted edge is constructed by the actual pullback universal property. -/
@[expose] def pair02 : Triple f ⟶ Double f :=
  pullback.lift (vertex0 f) (vertex2 f) (outer_condition f)

@[reassoc] lemma pair02_first : pair02 f ≫ first f = vertex0 f := pullback.lift_fst _ _ _
@[reassoc] lemma pair02_second : pair02 f ≫ second f = vertex2 f := pullback.lift_snd _ _ _

@[expose] def diagonal : U ⟶ Double f := pullback.lift (𝟙 U) (𝟙 U) (by simp)
@[reassoc] lemma diagonal_first : diagonal f ≫ first f = 𝟙 U := pullback.lift_fst _ _ _
@[reassoc] lemma diagonal_second : diagonal f ≫ second f = 𝟙 U := pullback.lift_snd _ _ _

variable (b : T ⟶ B)
abbrev localBase : U ⟶ B := f ≫ b
abbrev doubleBase : Double f ⟶ B := first f ≫ localBase f b
abbrev tripleBase : Triple f ⟶ B := pair01 f ≫ doubleBase f b

lemma second_base : second f ≫ localBase f b = doubleBase f b := by
  change second f ≫ (f ≫ b) = first f ≫ (f ≫ b)
  rw [← Category.assoc, ← Category.assoc, edge_condition]

lemma pair01_base : pair01 f ≫ doubleBase f b = tripleBase f b := rfl

lemma pair12_base : pair12 f ≫ doubleBase f b = tripleBase f b := by
  change pair12 f ≫ (first f ≫ localBase f b) = pair01 f ≫ doubleBase f b
  rw [← Category.assoc, ← middle_condition, Category.assoc, second_base]

lemma vertex0_base : vertex0 f ≫ localBase f b = tripleBase f b := Category.assoc _ _ _

lemma vertex1_base : vertex1 f ≫ localBase f b = tripleBase f b := by
  change (pair01 f ≫ second f) ≫ localBase f b = _
  rw [Category.assoc, second_base]

lemma vertex2_base : vertex2 f ≫ localBase f b = tripleBase f b := by
  change (pair12 f ≫ second f) ≫ localBase f b = _
  rw [Category.assoc, second_base, pair12_base]

lemma pair02_base : pair02 f ≫ doubleBase f b = tripleBase f b := by
  change pair02 f ≫ (first f ≫ localBase f b) = _
  rw [← Category.assoc, pair02_first, vertex0_base]

lemma diagonal_base : diagonal f ≫ doubleBase f b = localBase f b := by
  change diagonal f ≫ (first f ≫ localBase f b) = _
  rw [← Category.assoc, diagonal_first, Category.id_comp]
end ActualOverlapDiagram318
