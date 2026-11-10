module
public import RigidifiedPathTransport318
public section
noncomputable section
namespace RigidifiedCechNerve318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (square : e' ≫ f = g ≫ e)

/-- The actual induced map of categorical doubles, used as the section
map of the overlap. It exists for every pointed commuting square. -/
abbrev doubleSection := doubleMap f g e' e square
abbrev tripleSection := tripleMap f g e' e square

abbrev firstLine (L : RigidifiedLine e') :=
  RigidifiedPointedPullback318.line e' (doubleSection f g e e' square)
    (first f) (first g) (double_first f g e' e square) L
abbrev secondLine (L : RigidifiedLine e') :=
  RigidifiedPointedPullback318.line e' (doubleSection f g e e' square)
    (second f) (second g) (double_second f g e' e square) L

/-- A section map on an actual Čech overlap, not a tensor-spectrum or
abstract indexed overlap. Its two face maps are the original projections. -/
abbrev Overlap (L : RigidifiedLine e') :=
  CompatibleIso (doubleSection f g e e' square)
    (firstLine f g e e' square L) (secondLine f g e e' square L)

abbrev vertexLine₀ (L : RigidifiedLine e') :=
  RigidifiedPointedPullback318.line e' (tripleSection f g e e' square)
    (vertex0 f) (vertex0 g) (triple_vertex0 f g e' e square) L
abbrev vertexLine₁ (L : RigidifiedLine e') :=
  RigidifiedPointedPullback318.line e' (tripleSection f g e e' square)
    (vertex1 f) (vertex1 g) (triple_vertex1 f g e' e square) L
abbrev vertexLine₂ (L : RigidifiedLine e') :=
  RigidifiedPointedPullback318.line e' (tripleSection f g e e' square)
    (vertex2 f) (vertex2 g) (triple_vertex2 f g e' e square) L

/-- If the original square is a square of sections, the actual nerve maps
are sections as well. This records the section identity using only the
original fiber-product universal properties. -/
lemma double_section (p : X ⟶ S) (p' : X' ⟶ S')
    (hs' : e' ≫ p' = 𝟙 S')
    (hp : p' ≫ g = f ≫ p) :
    doubleSection f g e e' square ≫ doubleMap g f p' p hp = 𝟙 (Double g) := by
  apply pullback.hom_ext
  · rw [Category.assoc,double_first,← Category.assoc,double_first,
      Category.assoc,hs',Category.comp_id,Category.id_comp]
  · rw [Category.assoc,double_second,← Category.assoc,double_second,
      Category.assoc,hs',Category.comp_id,Category.id_comp]
end RigidifiedCechNerve318
