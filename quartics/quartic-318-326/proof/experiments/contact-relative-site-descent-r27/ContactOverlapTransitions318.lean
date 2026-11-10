module
public import ActualOverlapDiagram318
public import ContactRigidifiedPathComparison318
public section
noncomputable section
namespace ContactOverlapTransitions318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318 RigidifiedRelativeClass318
open ContactUniversalRigidifiedClass318 ContactTestRigidifiedCoherence318
open ActualOverlapDiagram318
variable (t : ℚ) {U T : Scheme} (f : U ⟶ T) (b : T ⟶ FieldBase t)

abbrev Left (L : RigidifiedLine (testSection t (localBase f b))) :=
  pullbackLine t (localBase f b) (doubleBase f b) (first f) rfl L
abbrev Right (L : RigidifiedLine (testSection t (localBase f b))) :=
  pullbackLine t (localBase f b) (doubleBase f b) (second f) (second_base f b) L

/-- Equality of the two actual original relative classes on the double overlap.
No descent object or effective-gluing conclusion is included in this condition. -/
@[expose] def Matching (L : RigidifiedLine (testSection t (localBase f b))) : Prop :=
  relativeClass (pullback.snd (q t) (doubleBase f b)) (testSection t (doubleBase f b))
      (Left t f b L) =
    relativeClass (pullback.snd (q t) (doubleBase f b)) (testSection t (doubleBase f b))
      (Right t f b L)

/-- The matching condition supplies an actual rigidification-compatible
isomorphism on the entire double-overlap family. -/
@[expose] def overlapIso (L : RigidifiedLine (testSection t (localBase f b)))
    (h : Matching t f b L) :
    CompatibleIso (testSection t (doubleBase f b)) (Left t f b L) (Right t f b L) :=
  transition t (doubleBase f b) h

lemma matching_iff_compatible (L : RigidifiedLine (testSection t (localBase f b))) :
    Matching t f b L ↔
      Nonempty (CompatibleIso (testSection t (doubleBase f b)) (Left t f b L) (Right t f b L)) :=
  relative_eq_iff_compatible _ _
    (RelativeSectionBaseChange318.sectionOn_snd (q t) (e t) (section_eq t) (doubleBase f b))
    (test_evaluation_bijective t (doubleBase f b)) _ _

abbrev Vertex (L : RigidifiedLine (testSection t (localBase f b)))
    (v : Triple f ⟶ U) (hv : v ≫ localBase f b = tripleBase f b) :=
  pullbackLine t (localBase f b) (tripleBase f b) v hv L

/-- Pull an actual overlap isomorphism to a named triple edge, then compare
its two iterated pullbacks with the two direct vertex pullbacks. Both path
comparisons are explicit actual compatible isomorphisms, selected by rigidity.
No equality with a canonical unrigidified associator is assumed. -/
@[expose] def edge (L : RigidifiedLine (testSection t (localBase f b)))
    (τ : CompatibleIso (testSection t (doubleBase f b)) (Left t f b L) (Right t f b L))
    (z : Triple f ⟶ Double f) (hz : z ≫ doubleBase f b = tripleBase f b)
    (v w : Triple f ⟶ U) (hv : v ≫ localBase f b = tripleBase f b)
    (hw : w ≫ localBase f b = tripleBase f b)
    (front : z ≫ first f = v) (back : z ≫ second f = w) :
    CompatibleIso (testSection t (tripleBase f b)) (Vertex t f b L v hv) (Vertex t f b L w hw) :=
  RigidifiedIsoCoherence318.compose _
    (RigidifiedIsoCoherence318.inverse _
      (ContactRigidifiedPathComparison318.pathIso t
        (localBase f b) (doubleBase f b) (tripleBase f b)
        (first f) z v rfl hz hv front L))
    (RigidifiedIsoCoherence318.compose _
      (pullbackIso t (doubleBase f b) (tripleBase f b) z hz τ)
      (ContactRigidifiedPathComparison318.pathIso t
        (localBase f b) (doubleBase f b) (tripleBase f b)
        (second f) z w (second_base f b) hz hw back L))

@[expose] def edge01 (L : RigidifiedLine (testSection t (localBase f b)))
    (τ : CompatibleIso (testSection t (doubleBase f b)) (Left t f b L) (Right t f b L)) :
    CompatibleIso (testSection t (tripleBase f b))
      (Vertex t f b L (vertex0 f) (vertex0_base f b))
      (Vertex t f b L (vertex1 f) (vertex1_base f b)) :=
  edge t f b L τ (pair01 f) (pair01_base f b) (vertex0 f) (vertex1 f)
    (vertex0_base f b) (vertex1_base f b) rfl rfl

@[expose] def edge12 (L : RigidifiedLine (testSection t (localBase f b)))
    (τ : CompatibleIso (testSection t (doubleBase f b)) (Left t f b L) (Right t f b L)) :
    CompatibleIso (testSection t (tripleBase f b))
      (Vertex t f b L (vertex1 f) (vertex1_base f b))
      (Vertex t f b L (vertex2 f) (vertex2_base f b)) :=
  edge t f b L τ (pair12 f) (pair12_base f b) (vertex1 f) (vertex2 f)
    (vertex1_base f b) (vertex2_base f b) (middle_condition f).symm rfl

@[expose] def edge02 (L : RigidifiedLine (testSection t (localBase f b)))
    (τ : CompatibleIso (testSection t (doubleBase f b)) (Left t f b L) (Right t f b L)) :
    CompatibleIso (testSection t (tripleBase f b))
      (Vertex t f b L (vertex0 f) (vertex0_base f b))
      (Vertex t f b L (vertex2 f) (vertex2_base f b)) :=
  edge t f b L τ (pair02 f) (pair02_base f b) (vertex0 f) (vertex2 f)
    (vertex0_base f b) (vertex2_base f b) (pair02_first f) (pair02_second f)

/-- The genuine triple-overlap cocycle equation for the explicitly normalized
edges. Its equality is on the actual module-sheaf morphisms. The normalization
uses `pathIso`, whose canonical-associator comparison remains separate. -/
theorem triple_cocycle (L : RigidifiedLine (testSection t (localBase f b)))
    (τ : CompatibleIso (testSection t (doubleBase f b)) (Left t f b L) (Right t f b L)) :
    (edge01 t f b L τ).iso.hom ≫ (edge12 t f b L τ).iso.hom =
      (edge02 t f b L τ).iso.hom := by
  have hc : RigidifiedIsoCoherence318.compose (testSection t (tripleBase f b))
      (edge01 t f b L τ) (edge12 t f b L τ) = edge02 t f b L τ :=
    compatible_unique (testSection t (tripleBase f b))
      (test_evaluation_bijective t (tripleBase f b)).injective _ _ _ _
  exact congrArg (fun k : CompatibleIso (testSection t (tripleBase f b))
      (Vertex t f b L (vertex0 f) (vertex0_base f b))
      (Vertex t f b L (vertex2 f) (vertex2_base f b)) => k.iso.hom) hc

/-- A class-level matching condition is sufficient for an actual overlap
isomorphism whose explicitly compared triple edges satisfy the cocycle. -/
theorem matching_triple_cocycle (L : RigidifiedLine (testSection t (localBase f b)))
    (h : Matching t f b L) :
    (edge01 t f b L (overlapIso t f b L h)).iso.hom ≫
      (edge12 t f b L (overlapIso t f b L h)).iso.hom =
        (edge02 t f b L (overlapIso t f b L h)).iso.hom :=
  triple_cocycle t f b L (overlapIso t f b L h)

/-- No choice of a different rigidification-compatible overlap isomorphism
can change the actual overlap map. -/
theorem overlap_unique (L : RigidifiedLine (testSection t (localBase f b)))
    (τ σ : CompatibleIso (testSection t (doubleBase f b)) (Left t f b L) (Right t f b L)) :
    τ = σ :=
  compatible_unique (testSection t (doubleBase f b))
    (test_evaluation_bijective t (doubleBase f b)).injective _ _ τ σ
end ContactOverlapTransitions318
