module
public import ModuleGlobalSections318
public import StructurePushforwardSplit318
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public section
noncomputable section
namespace ClutchedModule318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
abbrev unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- Multiplication by an actual global regular function as an O-linear sheaf map. -/
@[expose] def multiply {X : Scheme.{u}} (a : Γ(X,⊤)) : unit X ⟶ unit X :=
  ModuleGlobalSections318.ofTop (unit X) a

theorem multiply_apply {X : Scheme.{u}} (a : Γ(X,⊤)) (U : X.Opens) (x : Γ(X,U)) :
    (multiply a).app U x=x*(X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op a) :=
  ModuleGlobalSections318.ofTop_apply (unit X) a U x

theorem multiply_top {X : Scheme.{u}} (a x : Γ(X,⊤)) : (multiply a).app ⊤ x=x*a := by
  rw [multiply_apply]
  change x*(X.presheaf.map (𝟙 (op ⊤)) a)=x*a
  rw [CategoryTheory.Functor.map_id,ConcreteCategory.id_apply]

theorem multiply_isIso {X : Scheme.{u}} (a : Γ(X,⊤)) (ha : IsUnit a) : IsIso (multiply a) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hu := ha.map (X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op).hom
  change Function.Bijective (fun x : Γ(X,U) => (multiply a).app U x)
  simp only [multiply_apply]
  exact IsUnit.isUnit_iff_mulRight_bijective.mp hu

variable {X Y Z : Scheme.{u}} (j : Y ⟶ X) (k : Z ⟶ Y)
/-- Actual restriction of a chart's structure sheaf to a smaller chart,
viewed as modules on the ambient scheme. -/
@[expose] def restriction : (Scheme.Modules.pushforward j).obj (unit Y) ⟶
    (Scheme.Modules.pushforward (k≫j)).obj (unit Z) :=
  (Scheme.Modules.pushforward j).map (StructurePushforwardSplit318.unitMap k) ≫
    (Scheme.Modules.pushforwardComp k j).hom.app (unit Z)

theorem restriction_app (U : X.Opens) (x : Γ(Y,j⁻¹ᵁ U)) :
    (restriction j k).app U x=k.app (j⁻¹ᵁ U) x := rfl

variable {Y₀ Y₁ W : Scheme.{u}}
    (j₀ : Y₀ ⟶ X) (j₁ : Y₁ ⟶ X) (k₀ : W ⟶ Y₀) (k₁ : W ⟶ Y₁)
    (h : k₁≫j₁=k₀≫j₀) (a : Γ(W,⊤))

/-- The second restriction includes the specified transition multiplication
and the actual equality of its two routes into the ambient scheme. -/
@[expose] def twistedRestriction : (Scheme.Modules.pushforward j₁).obj (unit Y₁) ⟶
    (Scheme.Modules.pushforward (k₀≫j₀)).obj (unit W) :=
  restriction j₁ k₁ ≫ (Scheme.Modules.pushforwardCongr h).hom.app (unit W) ≫
    (Scheme.Modules.pushforward (k₀≫j₀)).map (multiply a)

theorem twistedRestriction_top (x : Γ(Y₁,⊤)) :
    (twistedRestriction j₀ j₁ k₀ k₁ h a).app ⊤ x=k₁.appTop x*a := by
  change (multiply a).app ⊤
    ((unit W).presheaf.map (𝟙 (op ⊤)) (k₁.appTop x))=_
  rw [CategoryTheory.Functor.map_id,ConcreteCategory.id_apply,multiply_top]

/-- A genuine sheaf of modules consisting of compatible local coefficients.
Local freeness is a separate theorem, not part of this definition. -/
@[expose] def sheaf : X.Modules :=
  pullback (restriction j₀ k₀) (twistedRestriction j₀ j₁ k₀ k₁ h a)

@[expose] def first : sheaf j₀ j₁ k₀ k₁ h a ⟶ (Scheme.Modules.pushforward j₀).obj (unit Y₀) :=
  pullback.fst _ _
@[expose] def second : sheaf j₀ j₁ k₀ k₁ h a ⟶ (Scheme.Modules.pushforward j₁).obj (unit Y₁) :=
  pullback.snd _ _

theorem compatibility : first j₀ j₁ k₀ k₁ h a ≫ restriction j₀ k₀ =
    second j₀ j₁ k₀ k₁ h a ≫ twistedRestriction j₀ j₁ k₀ k₁ h a := pullback.condition

/-- The exact sheaf universal property for compatible pairs of morphisms. -/
@[expose] def lift {M : X.Modules}
    (f : M ⟶ (Scheme.Modules.pushforward j₀).obj (unit Y₀))
    (g : M ⟶ (Scheme.Modules.pushforward j₁).obj (unit Y₁))
    (H : f≫restriction j₀ k₀=g≫twistedRestriction j₀ j₁ k₀ k₁ h a) :
    M ⟶ sheaf j₀ j₁ k₀ k₁ h a := pullback.lift f g H

theorem lift_first {M : X.Modules}
    (f : M ⟶ (Scheme.Modules.pushforward j₀).obj (unit Y₀))
    (g : M ⟶ (Scheme.Modules.pushforward j₁).obj (unit Y₁))
    (H : f≫restriction j₀ k₀=g≫twistedRestriction j₀ j₁ k₀ k₁ h a) :
    lift j₀ j₁ k₀ k₁ h a f g H≫first j₀ j₁ k₀ k₁ h a=f := pullback.lift_fst _ _ _

theorem lift_second {M : X.Modules}
    (f : M ⟶ (Scheme.Modules.pushforward j₀).obj (unit Y₀))
    (g : M ⟶ (Scheme.Modules.pushforward j₁).obj (unit Y₁))
    (H : f≫restriction j₀ k₀=g≫twistedRestriction j₀ j₁ k₀ k₁ h a) :
    lift j₀ j₁ k₀ k₁ h a f g H≫second j₀ j₁ k₀ k₁ h a=g := pullback.lift_snd _ _ _
end ClutchedModule318
