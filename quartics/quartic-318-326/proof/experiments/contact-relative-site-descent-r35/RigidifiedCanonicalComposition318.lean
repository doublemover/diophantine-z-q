module
public import PointedPullbackComposition318
public import PullbackUnitComposition318
public section
noncomputable section
namespace RigidifiedCanonicalComposition318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318 RigidifiedLineIsomorphism318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
universe u
variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
  (e₀ : S₀ ⟶ X₀) (e₁ : S₁ ⟶ X₁) (e₂ : S₂ ⟶ X₂)
  (a₁ : X₁ ⟶ X₀) (a₂ : X₂ ⟶ X₁)
  (b₁ : S₁ ⟶ S₀) (b₂ : S₂ ⟶ S₁)
  (h₁ : e₁ ≫ a₁ = b₁ ≫ e₀) (h₂ : e₂ ≫ a₂ = b₂ ≫ e₁)

/-- The canonical original module-pullback composition isomorphism itself
preserves the transported rigidifications. There is no scalar correction,
choice from a class equality, or global-function hypothesis in this result. -/
@[expose] def compositionIso (L : RigidifiedLine e₀) :
    CompatibleIso e₂
      (RigidifiedPointedPullback318.line e₁ e₂ a₂ b₂ h₂
        (RigidifiedPointedPullback318.line e₀ e₁ a₁ b₁ h₁ L))
      (RigidifiedPointedPullback318.line e₀ e₂ (a₂ ≫ a₁) (b₂ ≫ b₁)
        (PointedPullbackComposition318.composite_pointed e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂) L) where
  iso := (Scheme.Modules.pullbackComp a₂ a₁).app L.line.object
  commutes := by
    let ρ : (Scheme.Modules.pullback e₀).obj L.line.object ≅
        SheafOfModules.unit S₀.ringCatSheaf := L.trivialization
    have hn :
        (Scheme.Modules.pullbackComp b₂ b₁).hom.app
            ((Scheme.Modules.pullback e₀).obj L.line.object) ≫
          (Scheme.Modules.pullback (b₂ ≫ b₁)).map ρ.hom ≫
          (IdentityCotangent318.pullbackUnitIso (b₂ ≫ b₁)).hom =
        (Scheme.Modules.pullback b₂).map ((Scheme.Modules.pullback b₁).map ρ.hom) ≫
          (Scheme.Modules.pullback b₂).map (IdentityCotangent318.pullbackUnitIso b₁).hom ≫
          (IdentityCotangent318.pullbackUnitIso b₂).hom := by
      rw [← Category.assoc, ← (Scheme.Modules.pullbackComp b₂ b₁).hom.naturality
        ρ.hom, Category.assoc, PullbackUnitComposition318.composition]
      simp only [Functor.comp_map]
    change (Scheme.Modules.pullback e₂).map ((Scheme.Modules.pullbackComp a₂ a₁).hom.app L.line.object) ≫
      (RigidifiedPointedPullback318.restrictionComparison e₀ e₂ (a₂ ≫ a₁) (b₂ ≫ b₁)
        (PointedPullbackComposition318.composite_pointed e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂)).hom.app L.line.object ≫
      (Scheme.Modules.pullback (b₂ ≫ b₁)).map ρ.hom ≫
      (IdentityCotangent318.pullbackUnitIso (b₂ ≫ b₁)).hom =
    (RigidifiedPointedPullback318.restrictionComparison e₁ e₂ a₂ b₂ h₂).hom.app
        ((Scheme.Modules.pullback a₁).obj L.line.object) ≫
      (Scheme.Modules.pullback b₂).map
        ((RigidifiedPointedPullback318.restrictionComparison e₀ e₁ a₁ b₁ h₁).hom.app L.line.object ≫
          (Scheme.Modules.pullback b₁).map ρ.hom ≫
          (IdentityCotangent318.pullbackUnitIso b₁).hom) ≫
      (IdentityCotangent318.pullbackUnitIso b₂).hom
    calc
      _ = (RigidifiedPointedPullback318.restrictionComparison e₁ e₂ a₂ b₂ h₂).hom.app
            ((Scheme.Modules.pullback a₁).obj L.line.object) ≫
          (Scheme.Modules.pullback b₂).map
            ((RigidifiedPointedPullback318.restrictionComparison e₀ e₁ a₁ b₁ h₁).hom.app L.line.object) ≫
          (Scheme.Modules.pullbackComp b₂ b₁).hom.app
            ((Scheme.Modules.pullback e₀).obj L.line.object) ≫
          (Scheme.Modules.pullback (b₂ ≫ b₁)).map ρ.hom ≫
          (IdentityCotangent318.pullbackUnitIso (b₂ ≫ b₁)).hom := by
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ (Scheme.Modules.pullback (b₂ ≫ b₁)).map ρ.hom ≫
            (IdentityCotangent318.pullbackUnitIso (b₂ ≫ b₁)).hom)
          (PointedPullbackComposition318.restriction_composition
            e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂ L.line.object)
      _ = _ := by
        rw [hn]
        simp only [Functor.map_comp, Category.assoc]

/-- The underlying map is literally the original pullback composition map. -/
lemma compositionIso_hom (L : RigidifiedLine e₀) :
    (compositionIso e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂ L).iso.hom =
      (Scheme.Modules.pullbackComp a₂ a₁).hom.app L.line.object := rfl
/-- The same canonical comparison with explicitly named composite maps.
The only transport is along the supplied equalities of actual scheme maps. -/
@[expose] def compositionAlong (a₀₂ : X₂ ⟶ X₀) (b₀₂ : S₂ ⟶ S₀)
    (ha : a₂ ≫ a₁ = a₀₂) (hb : b₂ ≫ b₁ = b₀₂)
    (hc : e₂ ≫ a₀₂ = b₀₂ ≫ e₀) (L : RigidifiedLine e₀) :
    CompatibleIso e₂
      (RigidifiedPointedPullback318.line e₁ e₂ a₂ b₂ h₂
        (RigidifiedPointedPullback318.line e₀ e₁ a₁ b₁ h₁ L))
      (RigidifiedPointedPullback318.line e₀ e₂ a₀₂ b₀₂ hc L) := by
  subst a₀₂
  subst b₀₂
  exact compositionIso e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂ L

lemma compositionAlong_hom (a₀₂ : X₂ ⟶ X₀) (b₀₂ : S₂ ⟶ S₀)
    (ha : a₂ ≫ a₁ = a₀₂) (hb : b₂ ≫ b₁ = b₀₂)
    (hc : e₂ ≫ a₀₂ = b₀₂ ≫ e₀) (L : RigidifiedLine e₀) :
    (compositionAlong e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂ a₀₂ b₀₂ ha hb hc L).iso.hom =
      (PullbackPathComposition318.iso a₂ a₁ a₀₂ ha).hom.app L.line.object := by
  subst a₀₂
  subst b₀₂
  simp [compositionAlong, compositionIso, PullbackPathComposition318.iso,
    Scheme.Modules.pullbackCongr]
end RigidifiedCanonicalComposition318
