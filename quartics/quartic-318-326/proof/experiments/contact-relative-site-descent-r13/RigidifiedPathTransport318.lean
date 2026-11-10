module
public import RigidifiedCanonicalComposition318
public import RigidifiedRelativeEffectivity318
public section
noncomputable section
namespace RigidifiedPathTransport318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318 RigidifiedLineIsomorphism318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {U X Y A B C : Scheme.{u}} (eU : A ⟶ U) (eX : B ⟶ X) (eY : C ⟶ Y)
  (p₀ p₁ : X ⟶ U) (b₀ b₁ : B ⟶ A) (q : Y ⟶ X) (a : C ⟶ B)
  (hp₀ : eX ≫ p₀ = b₀ ≫ eU) (hp₁ : eX ≫ p₁ = b₁ ≫ eU)
  (hq : eY ≫ q = a ≫ eX)
  (v₀ v₁ : Y ⟶ U) (c₀ c₁ : C ⟶ A)
  (h₀ : q ≫ p₀ = v₀) (h₁ : q ≫ p₁ = v₁)
  (hb₀ : a ≫ b₀ = c₀) (hb₁ : a ≫ b₁ = c₁)
  (hv₀ : eY ≫ v₀ = c₀ ≫ eU) (hv₁ : eY ≫ v₁ = c₁ ≫ eU)
  (L : RigidifiedLine eU)
  (τ : CompatibleIso eX
    (RigidifiedPointedPullback318.line eU eX p₀ b₀ hp₀ L)
    (RigidifiedPointedPullback318.line eU eX p₁ b₁ hp₁ L))

/-- Original sheaf path normalization preserves the actual rigidification,
with both endpoint comparisons the canonical ones, not arbitrary isomorphisms. -/
@[expose] def transport : CompatibleIso eY
    (RigidifiedPointedPullback318.line eU eY v₀ c₀ hv₀ L)
    (RigidifiedPointedPullback318.line eU eY v₁ c₁ hv₁ L) :=
  RigidifiedIsoCoherence318.compose eY
    (RigidifiedIsoCoherence318.inverse eY
      (RigidifiedCanonicalComposition318.compositionAlong eU eX eY p₀ q b₀ a hp₀ hq
        v₀ c₀ h₀ hb₀ hv₀ L))
    (RigidifiedIsoCoherence318.compose eY
      (RigidifiedPointedPullback318.mapIso eX eY q a hq τ)
      (RigidifiedCanonicalComposition318.compositionAlong eU eX eY p₁ q b₁ a hp₁ hq
        v₁ c₁ h₁ hb₁ hv₁ L))

lemma transport_hom :
    (transport eU eX eY p₀ p₁ b₀ b₁ q a hp₀ hp₁ hq v₀ v₁ c₀ c₁
      h₀ h₁ hb₀ hb₁ hv₀ hv₁ L τ).iso.hom =
    SheafPathTransport318.transport L.line.object q p₀ p₁ v₀ v₁ h₀ h₁ τ.iso.hom := by
  have hi : (RigidifiedCanonicalComposition318.compositionAlong eU eX eY p₀ q b₀ a hp₀ hq
      v₀ c₀ h₀ hb₀ hv₀ L).iso =
      (PullbackPathComposition318.iso q p₀ v₀ h₀).app L.line.object :=
    Iso.ext (RigidifiedCanonicalComposition318.compositionAlong_hom
      eU eX eY p₀ q b₀ a hp₀ hq v₀ c₀ h₀ hb₀ hv₀ L)
  have hh := RigidifiedCanonicalComposition318.compositionAlong_hom
    eU eX eY p₁ q b₁ a hp₁ hq v₁ c₁ h₁ hb₁ hv₁ L
  change (RigidifiedCanonicalComposition318.compositionAlong eU eX eY p₀ q b₀ a hp₀ hq
      v₀ c₀ h₀ hb₀ hv₀ L).iso.inv ≫
      (Scheme.Modules.pullback q).map τ.iso.hom ≫
      (RigidifiedCanonicalComposition318.compositionAlong eU eX eY p₁ q b₁ a hp₁ hq
        v₁ c₁ h₁ hb₁ hv₁ L).iso.hom = _
  rw [hi,hh] <;> rfl
end RigidifiedPathTransport318
