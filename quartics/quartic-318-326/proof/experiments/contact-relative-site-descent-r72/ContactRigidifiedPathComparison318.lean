module
public import ContactTestRigidifiedCoherence318
public section
noncomputable section
namespace ContactRigidifiedPathComparison318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318 RigidifiedRelativeClass318
open ContactUniversalRigidifiedClass318 ContactTestRigidifiedCoherence318
variable (t : ℚ) {T₀ T₁ T₂ : Scheme}

/-- Iterated actual rigidified pullback has the same original relative class
as direct pullback along the composite test map. -/
lemma composition_class (b₀ : T₀ ⟶ FieldBase t) (b₁ : T₁ ⟶ FieldBase t)
    (b₂ : T₂ ⟶ FieldBase t) (a : T₁ ⟶ T₀) (a' : T₂ ⟶ T₁)
    (ha : a ≫ b₀ = b₁) (ha' : a' ≫ b₁ = b₂)
    (hc : (a' ≫ a) ≫ b₀ = b₂) (L : RigidifiedLine (testSection t b₀)) :
    relativeClass (pullback.snd (q t) b₂) (testSection t b₂)
        (pullbackLine t b₁ b₂ a' ha' (pullbackLine t b₀ b₁ a ha L)) =
      relativeClass (pullback.snd (q t) b₂) (testSection t b₂)
        (pullbackLine t b₀ b₂ (a' ≫ a) hc L) := by
  change RelativeLineClassBaseChange318.testMap (q t) b₁ b₂ a' ha'
      (RelativeLineClassBaseChange318.testMap (q t) b₀ b₁ a ha
        (relativeClass (pullback.snd (q t) b₀) (testSection t b₀) L)) =
    RelativeLineClassBaseChange318.testMap (q t) b₀ b₂ (a' ≫ a) hc
        (relativeClass (pullback.snd (q t) b₀) (testSection t b₀) L)
  exact congrArg (fun F : RelativeLineClassBaseChange318.TestClass (q t) b₀ →*
      RelativeLineClassBaseChange318.TestClass (q t) b₂ =>
      F (relativeClass (pullback.snd (q t) b₀) (testSection t b₀) L))
    (RelativeLineClassBaseChange318.testMap_composition (q t) b₀ b₁ b₂ a a' ha ha' hc).symm

/-- Comparison to any named map equal to the composite. This makes overlap
endpoint identities explicit instead of changing test schemes silently. -/
lemma path_class (b₀ : T₀ ⟶ FieldBase t) (b₁ : T₁ ⟶ FieldBase t)
    (b₂ : T₂ ⟶ FieldBase t) (a : T₁ ⟶ T₀) (a' : T₂ ⟶ T₁) (c : T₂ ⟶ T₀)
    (ha : a ≫ b₀ = b₁) (ha' : a' ≫ b₁ = b₂) (hc : c ≫ b₀ = b₂)
    (path : a' ≫ a = c) (L : RigidifiedLine (testSection t b₀)) :
    relativeClass (pullback.snd (q t) b₂) (testSection t b₂)
        (pullbackLine t b₁ b₂ a' ha' (pullbackLine t b₀ b₁ a ha L)) =
      relativeClass (pullback.snd (q t) b₂) (testSection t b₂)
        (pullbackLine t b₀ b₂ c hc L) := by
  subst c
  exact composition_class t b₀ b₁ b₂ a a' ha ha' hc L

/-- An actual compatible path comparison selected by rigidity. Its existence
is proved; identification with the unrigidified canonical pullback associator
is deliberately a separate obligation. -/
@[expose] def pathIso (b₀ : T₀ ⟶ FieldBase t) (b₁ : T₁ ⟶ FieldBase t)
    (b₂ : T₂ ⟶ FieldBase t) (a : T₁ ⟶ T₀) (a' : T₂ ⟶ T₁) (c : T₂ ⟶ T₀)
    (ha : a ≫ b₀ = b₁) (ha' : a' ≫ b₁ = b₂) (hc : c ≫ b₀ = b₂)
    (path : a' ≫ a = c) (L : RigidifiedLine (testSection t b₀)) :
    CompatibleIso (testSection t b₂)
      (pullbackLine t b₁ b₂ a' ha' (pullbackLine t b₀ b₁ a ha L))
      (pullbackLine t b₀ b₂ c hc L) :=
  transition t b₂ (path_class t b₀ b₁ b₂ a a' c ha ha' hc path L)
end ContactRigidifiedPathComparison318
