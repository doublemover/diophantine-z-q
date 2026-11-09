module
public import RigidifiedPointedPullback318
public import PullbackPathComposition318
public section
noncomputable section
namespace PointedPullbackComposition318
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
universe v u

/-- Cancellation of three actual isomorphism rectangles. This auxiliary
identity will be instantiated with the original pullback associativity maps. -/
lemma rectangles {C : Type u} [Category.{v} C]
    {A B C₀ D E F G H : C}
    (u : A ≅ B) (v : C₀ ≅ B) (w : C₀ ≅ D) (x : E ≅ D)
    (y : E ≅ F) (z : F ≅ G) (r : B ≅ G) (s : A ≅ H)
    (k : H ≅ G) (d : D ≅ G)
    (h₁ : u.hom ≫ r.hom = s.hom ≫ k.hom)
    (h₂ : v.hom ≫ r.hom = w.hom ≫ d.hom)
    (h₃ : y.hom ≫ z.hom = x.hom ≫ d.hom) :
    s.hom ≫ k.hom ≫ z.inv = u.hom ≫ v.inv ≫ w.hom ≫ x.inv ≫ y.hom := by
  apply (cancel_mono z.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₃, Iso.inv_hom_id_assoc, ← h₂, Iso.inv_hom_id_assoc]
  exact h₁.symm

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
  (e₀ : S₀ ⟶ X₀) (e₁ : S₁ ⟶ X₁) (e₂ : S₂ ⟶ X₂)
  (a₁ : X₁ ⟶ X₀) (a₂ : X₂ ⟶ X₁)
  (b₁ : S₁ ⟶ S₀) (b₂ : S₂ ⟶ S₁)
  (h₁ : e₁ ≫ a₁ = b₁ ≫ e₀) (h₂ : e₂ ≫ a₂ = b₂ ≫ e₁)

lemma composite_pointed : e₂ ≫ (a₂ ≫ a₁) = (b₂ ≫ b₁) ≫ e₀ := by
  rw [← Category.assoc, h₂, Category.assoc, h₁, ← Category.assoc]

/-- Express the existing actual pointed comparison using the named-path
comparison already proved coherent in the accepted baseline. -/
lemma restrictionComparison_eq {X S X' S' : Scheme.{u}}
    (e : S ⟶ X) (e' : S' ⟶ X') (a : X' ⟶ X) (b : S' ⟶ S)
    (h : e' ≫ a = b ≫ e) :
    RigidifiedPointedPullback318.restrictionComparison e e' a b h =
      PullbackPathComposition318.iso e' a (b ≫ e) h ≪≫
        (PullbackPathComposition318.iso b e (b ≫ e) rfl).symm := by
  apply Iso.ext
  ext M
  simp [RigidifiedPointedPullback318.restrictionComparison,
    PullbackPathComposition318.iso, Scheme.Modules.pullbackCongr]

/-- The original pointed restriction comparisons satisfy the composition
square for the original module-sheaf pullback associator. All three coherence
rectangles are instances of the accepted named-path associativity theorem. -/
lemma restriction_composition (M : X₀.Modules) :
    (Scheme.Modules.pullback e₂).map ((Scheme.Modules.pullbackComp a₂ a₁).hom.app M) ≫
      (RigidifiedPointedPullback318.restrictionComparison e₀ e₂ (a₂ ≫ a₁) (b₂ ≫ b₁)
        (composite_pointed e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂)).hom.app M =
    (RigidifiedPointedPullback318.restrictionComparison e₁ e₂ a₂ b₂ h₂).hom.app
        ((Scheme.Modules.pullback a₁).obj M) ≫
      (Scheme.Modules.pullback b₂).map
        ((RigidifiedPointedPullback318.restrictionComparison e₀ e₁ a₁ b₁ h₁).hom.app M) ≫
      (Scheme.Modules.pullbackComp b₂ b₁).hom.app ((Scheme.Modules.pullback e₀).obj M) := by
  let r : S₂ ⟶ X₀ := (b₂ ≫ b₁) ≫ e₀
  have hl : (b₂ ≫ e₁) ≫ a₁ = r := by
    dsimp [r]
    rw [Category.assoc, h₁, Category.assoc]
  have hr : b₂ ≫ (b₁ ≫ e₀) = r := (Category.assoc _ _ _).symm
  have hA := PullbackPathComposition318.assoc e₂ a₂ a₁
    (b₂ ≫ e₁) (a₂ ≫ a₁) r h₂ rfl hl
    (composite_pointed e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂) M
  have hB := PullbackPathComposition318.assoc b₂ e₁ a₁
    (b₂ ≫ e₁) (b₁ ≫ e₀) r rfl h₁ hl hr M
  have hC := PullbackPathComposition318.assoc b₂ b₁ e₀
    (b₂ ≫ b₁) (b₁ ≫ e₀) r rfl rfl rfl hr M
  have h := rectangles
    ((PullbackPathComposition318.iso e₂ a₂ (b₂ ≫ e₁) h₂).app
      ((Scheme.Modules.pullback a₁).obj M))
    ((PullbackPathComposition318.iso b₂ e₁ (b₂ ≫ e₁) rfl).app
      ((Scheme.Modules.pullback a₁).obj M))
    ((Scheme.Modules.pullback b₂).mapIso
      ((PullbackPathComposition318.iso e₁ a₁ (b₁ ≫ e₀) h₁).app M))
    ((Scheme.Modules.pullback b₂).mapIso
      ((PullbackPathComposition318.iso b₁ e₀ (b₁ ≫ e₀) rfl).app M))
    ((PullbackPathComposition318.iso b₂ b₁ (b₂ ≫ b₁) rfl).app
      ((Scheme.Modules.pullback e₀).obj M))
    ((PullbackPathComposition318.iso (b₂ ≫ b₁) e₀ r rfl).app M)
    ((PullbackPathComposition318.iso (b₂ ≫ e₁) a₁ r hl).app M)
    ((Scheme.Modules.pullback e₂).mapIso
      ((PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).app M))
    ((PullbackPathComposition318.iso e₂ (a₂ ≫ a₁) r
      (composite_pointed e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂)).app M)
    ((PullbackPathComposition318.iso b₂ (b₁ ≫ e₀) r hr).app M)
    hA hB hC
  rw [restrictionComparison_eq, restrictionComparison_eq, restrictionComparison_eq]
  simpa [PullbackPathComposition318.iso, Scheme.Modules.pullbackCongr,
    Functor.map_comp, Category.assoc, r] using h
end PointedPullbackComposition318
