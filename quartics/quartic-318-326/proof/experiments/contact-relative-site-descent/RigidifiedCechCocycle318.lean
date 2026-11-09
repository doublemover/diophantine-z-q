module
public import RigidifiedCechNerve318
public section
noncomputable section
namespace RigidifiedCechCocycle318
open AlgebraicGeometry CategoryTheory ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318 RigidifiedCechNerve318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (square : e' ≫ f = g ≫ e)
  (L : RigidifiedLine e') (τ : Overlap f g e e' square L)

@[expose] def edge01 : CompatibleIso (tripleSection f g e e' square)
    (vertexLine₀ f g e e' square L) (vertexLine₁ f g e e' square L) :=
  RigidifiedPathTransport318.transport e' (doubleSection f g e e' square)
    (tripleSection f g e e' square) (first f) (second f) (first g) (second g)
    (pair01 f) (pair01 g) (double_first f g e' e square) (double_second f g e' e square)
    (triple_pair01 f g e' e square) (vertex0 f) (vertex1 f) (vertex0 g) (vertex1 g)
    rfl rfl rfl rfl (triple_vertex0 f g e' e square) (triple_vertex1 f g e' e square) L τ

@[expose] def edge12 : CompatibleIso (tripleSection f g e e' square)
    (vertexLine₁ f g e e' square L) (vertexLine₂ f g e e' square L) :=
  RigidifiedPathTransport318.transport e' (doubleSection f g e e' square)
    (tripleSection f g e e' square) (first f) (second f) (first g) (second g)
    (pair12 f) (pair12 g) (double_first f g e' e square) (double_second f g e' e square)
    (triple_pair12 f g e' e square) (vertex1 f) (vertex2 f) (vertex1 g) (vertex2 g)
    (middle_condition f).symm rfl (middle_condition g).symm rfl
    (triple_vertex1 f g e' e square) (triple_vertex2 f g e' e square) L τ

@[expose] def edge02 : CompatibleIso (tripleSection f g e e' square)
    (vertexLine₀ f g e e' square L) (vertexLine₂ f g e e' square L) :=
  RigidifiedPathTransport318.transport e' (doubleSection f g e e' square)
    (tripleSection f g e e' square) (first f) (second f) (first g) (second g)
    (pair02 f) (pair02 g) (double_first f g e' e square) (double_second f g e' e square)
    (triple_pair02 f g e' e square) (vertex0 f) (vertex2 f) (vertex0 g) (vertex2 g)
    (pair02_first f) (pair02_second f) (pair02_first g) (pair02_second g)
    (triple_vertex0 f g e' e square) (triple_vertex2 f g e' e square) L τ

lemma edge01_hom : (edge01 f g e e' square L τ).iso.hom =
    OriginalSchemeDescentData318.edge01 f L.line τ.iso.hom :=
  RigidifiedPathTransport318.transport_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
lemma edge12_hom : (edge12 f g e e' square L τ).iso.hom =
    OriginalSchemeDescentData318.edge12 f L.line τ.iso.hom :=
  RigidifiedPathTransport318.transport_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
lemma edge02_hom : (edge02 f g e e' square L τ).iso.hom =
    OriginalSchemeDescentData318.edge02 f L.line τ.iso.hom :=
  RigidifiedPathTransport318.transport_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The original categorical triple law is derived from rigidity of the
actual triple section. It is not an input on a proposed overlap. -/
lemma cocycle (h : Function.Injective (tripleSection f g e e' square).appTop) :
    OriginalSchemeDescentData318.Cocycle f L.line τ.iso.hom := by
  have hh := compatible_unique (tripleSection f g e e' square) h
    (vertexLine₀ f g e e' square L) (vertexLine₂ f g e e' square L)
    (RigidifiedIsoCoherence318.compose _ (edge01 f g e e' square L τ) (edge12 f g e e' square L τ))
    (edge02 f g e e' square L τ)
  have hmap := congrArg (fun a => a.iso.hom) hh
  change (edge01 f g e e' square L τ).iso.hom ≫ (edge12 f g e e' square L τ).iso.hom =
    (edge02 f g e e' square L τ).iso.hom at hmap
  simpa only [edge01_hom,edge12_hom,edge02_hom,OriginalSchemeDescentData318.Cocycle] using hmap
end RigidifiedCechCocycle318
