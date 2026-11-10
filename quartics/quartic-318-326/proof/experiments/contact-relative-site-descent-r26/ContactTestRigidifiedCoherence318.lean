module
public import ContactUniversalRigidifiedClass318
public import RigidifiedPointedPullback318
public import RigidifiedClassQuotient318
public section
noncomputable section
namespace ContactTestRigidifiedCoherence318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318 RigidifiedRelativeClass318
open ContactUniversalRigidifiedClass318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {T T' : Scheme}

/-- Classification by actual compatible isomorphisms on every full original
scheme test, using the already proved universal structure-pushforward theorem. -/
@[expose] def classEquivalence (b : T ⟶ FieldBase t) :
    RigidifiedClassQuotient318.RigidifiedClass (testSection t b) ≃
      RelativeLineClassBaseChange318.TestClass (q t) b :=
  RigidifiedClassQuotient318.equivalence (testSection t b) (pullback.snd (q t) b)
    (RelativeSectionBaseChange318.sectionOn_snd (q t) (e t) (section_eq t) b)
    (test_evaluation_bijective t b)

/-- Actual rigidified pullback along the original map of full fiber products. -/
@[expose] def pullbackLine (b : T ⟶ FieldBase t) (b' : T' ⟶ FieldBase t)
    (a : T' ⟶ T) (ha : a ≫ b = b') (L : RigidifiedLine (testSection t b)) :
    RigidifiedLine (testSection t b') :=
  RigidifiedPointedPullback318.line (testSection t b) (testSection t b')
    (RelativeLineClassBaseChange318.totalMap (q t) b b' a ha) a
    (RelativeSectionBaseChange318.sectionOn_naturality (q t) (e t) (section_eq t) b b' a ha) L

@[expose] def pullbackIso (b : T ⟶ FieldBase t) (b' : T' ⟶ FieldBase t)
    (a : T' ⟶ T) (ha : a ≫ b = b') {L M : RigidifiedLine (testSection t b)}
    (f : CompatibleIso (testSection t b) L M) :
    CompatibleIso (testSection t b') (pullbackLine t b b' a ha L) (pullbackLine t b b' a ha M) :=
  RigidifiedPointedPullback318.mapIso (testSection t b) (testSection t b')
    (RelativeLineClassBaseChange318.totalMap (q t) b b' a ha) a
    (RelativeSectionBaseChange318.sectionOn_naturality (q t) (e t) (section_eq t) b b' a ha) f

lemma pullbackLine_class (b : T ⟶ FieldBase t) (b' : T' ⟶ FieldBase t)
    (a : T' ⟶ T) (ha : a ≫ b = b') (L : RigidifiedLine (testSection t b)) :
    relativeClass (pullback.snd (q t) b') (testSection t b') (pullbackLine t b b' a ha L) =
      RelativeLineClassBaseChange318.testMap (q t) b b' a ha
        (relativeClass (pullback.snd (q t) b) (testSection t b) L) := rfl

@[expose] def transition (b : T ⟶ FieldBase t) {L M : RigidifiedLine (testSection t b)}
    (h : relativeClass (pullback.snd (q t) b) (testSection t b) L =
      relativeClass (pullback.snd (q t) b) (testSection t b) M) :
    CompatibleIso (testSection t b) L M :=
  RigidifiedIsoCoherence318.transition (testSection t b) (pullback.snd (q t) b)
    (RelativeSectionBaseChange318.sectionOn_snd (q t) (e t) (section_eq t) b)
    (test_evaluation_bijective t b) h

/-- The actual cocycle equation holds on every scheme test, including the
nonreduced tests that can occur in descent overlap diagrams. -/
theorem transition_cocycle (b : T ⟶ FieldBase t)
    {L M N : RigidifiedLine (testSection t b)}
    (hLM : relativeClass (pullback.snd (q t) b) (testSection t b) L =
      relativeClass (pullback.snd (q t) b) (testSection t b) M)
    (hMN : relativeClass (pullback.snd (q t) b) (testSection t b) M =
      relativeClass (pullback.snd (q t) b) (testSection t b) N) :
    (transition t b hLM).iso.hom ≫ (transition t b hMN).iso.hom =
      (transition t b (hLM.trans hMN)).iso.hom :=
  RigidifiedIsoCoherence318.transition_hom_cocycle (testSection t b) (pullback.snd (q t) b)
    (RelativeSectionBaseChange318.sectionOn_snd (q t) (e t) (section_eq t) b)
    (test_evaluation_bijective t b) hLM hMN

/-- The chosen comparison on a further test is exactly the literal pullback
of the original comparison, not merely another isomorphism in its class. -/
theorem transition_pullback (b : T ⟶ FieldBase t) (b' : T' ⟶ FieldBase t)
    (a : T' ⟶ T) (ha : a ≫ b = b') {L M : RigidifiedLine (testSection t b)}
    (h : relativeClass (pullback.snd (q t) b) (testSection t b) L =
      relativeClass (pullback.snd (q t) b) (testSection t b) M) :
    pullbackIso t b b' a ha (transition t b h) =
      transition t b' (L := pullbackLine t b b' a ha L)
        (M := pullbackLine t b b' a ha M)
        (congrArg (RelativeLineClassBaseChange318.testMap (q t) b b' a ha) h) :=
  compatible_unique (testSection t b') (test_evaluation_bijective t b').injective _ _ _ _
end ContactTestRigidifiedCoherence318
