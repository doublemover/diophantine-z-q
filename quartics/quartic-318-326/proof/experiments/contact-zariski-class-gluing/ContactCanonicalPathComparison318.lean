module
public import RigidifiedCanonicalComposition318
public import ContactRigidifiedPathComparison318
public section
noncomputable section
namespace ContactCanonicalPathComparison318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318 RigidifiedRelativeClass318
open ContactUniversalRigidifiedClass318 ContactTestRigidifiedCoherence318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {T₀ T₁ T₂ : Scheme}
  (b₀ : T₀ ⟶ FieldBase t) (b₁ : T₁ ⟶ FieldBase t) (b₂ : T₂ ⟶ FieldBase t)
  (a : T₁ ⟶ T₀) (a' : T₂ ⟶ T₁) (c : T₂ ⟶ T₀)
  (ha : a ≫ b₀ = b₁) (ha' : a' ≫ b₁ = b₂) (hc : c ≫ b₀ = b₂)
  (path : a' ≫ a = c)

include path in
lemma total_path :
    RelativeLineClassBaseChange318.totalMap (q t) b₁ b₂ a' ha' ≫
      RelativeLineClassBaseChange318.totalMap (q t) b₀ b₁ a ha =
        RelativeLineClassBaseChange318.totalMap (q t) b₀ b₂ c hc := by
  subst c
  exact (RelativeLineClassBaseChange318.totalMap_composition (q t) b₀ b₁ b₂ a a' ha ha' hc).symm

/-- The canonical original module-pullback comparison on the exact relative
fiber-product maps is compatible with the actual transported rigidifications. -/
@[expose] def canonicalPathIso (L : RigidifiedLine (testSection t b₀)) :
    CompatibleIso (testSection t b₂)
      (pullbackLine t b₁ b₂ a' ha' (pullbackLine t b₀ b₁ a ha L))
      (pullbackLine t b₀ b₂ c hc L) :=
  RigidifiedCanonicalComposition318.compositionAlong
    (testSection t b₀) (testSection t b₁) (testSection t b₂)
    (RelativeLineClassBaseChange318.totalMap (q t) b₀ b₁ a ha)
    (RelativeLineClassBaseChange318.totalMap (q t) b₁ b₂ a' ha') a a'
    (RelativeSectionBaseChange318.sectionOn_naturality (q t) (e t) (section_eq t) b₀ b₁ a ha)
    (RelativeSectionBaseChange318.sectionOn_naturality (q t) (e t) (section_eq t) b₁ b₂ a' ha')
    (RelativeLineClassBaseChange318.totalMap (q t) b₀ b₂ c hc) c
    (total_path t b₀ b₁ b₂ a a' c ha ha' hc path) path
    (RelativeSectionBaseChange318.sectionOn_naturality (q t) (e t) (section_eq t) b₀ b₂ c hc) L

/-- The path isomorphism previously selected by rigidity is exactly this
canonical original module-sheaf composition/equality comparison. -/
theorem pathIso_eq_canonical (L : RigidifiedLine (testSection t b₀)) :
    ContactRigidifiedPathComparison318.pathIso t b₀ b₁ b₂ a a' c ha ha' hc path L =
      canonicalPathIso t b₀ b₁ b₂ a a' c ha ha' hc path L :=
  compatible_unique (testSection t b₂) (test_evaluation_bijective t b₂).injective _ _ _ _

/-- The exact underlying original sheaf map, with the actual total-map path
identity explicitly exposed for descent consumers. -/
lemma pathIso_hom (L : RigidifiedLine (testSection t b₀)) :
    (ContactRigidifiedPathComparison318.pathIso t b₀ b₁ b₂ a a' c ha ha' hc path L).iso.hom =
      (PullbackPathComposition318.iso
        (RelativeLineClassBaseChange318.totalMap (q t) b₁ b₂ a' ha')
        (RelativeLineClassBaseChange318.totalMap (q t) b₀ b₁ a ha)
        (RelativeLineClassBaseChange318.totalMap (q t) b₀ b₂ c hc)
        (total_path t b₀ b₁ b₂ a a' c ha ha' hc path)).hom.app L.line.object := by
  rw [pathIso_eq_canonical]
  exact RigidifiedCanonicalComposition318.compositionAlong_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
/-- The complete original isomorphism, including its inverse, is identified.
This allows both normalizing directions in the overlap cocycle to use the
canonical module-pullback comparison. -/
lemma pathIso_iso (L : RigidifiedLine (testSection t b₀)) :
    (ContactRigidifiedPathComparison318.pathIso t b₀ b₁ b₂ a a' c ha ha' hc path L).iso =
      (PullbackPathComposition318.iso
        (RelativeLineClassBaseChange318.totalMap (q t) b₁ b₂ a' ha')
        (RelativeLineClassBaseChange318.totalMap (q t) b₀ b₁ a ha)
        (RelativeLineClassBaseChange318.totalMap (q t) b₀ b₂ c hc)
        (total_path t b₀ b₁ b₂ a a' c ha ha' hc path)).app L.line.object := by
  apply Iso.ext
  exact pathIso_hom t b₀ b₁ b₂ a a' c ha ha' hc path L
end ContactCanonicalPathComparison318
