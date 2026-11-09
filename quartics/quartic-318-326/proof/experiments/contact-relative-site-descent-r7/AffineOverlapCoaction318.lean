module
public import AffineModuleMate318
public import Mathlib.CategoryTheory.HomCongr
public section
noncomputable section
namespace AffineOverlapCoaction318
open CategoryTheory TensorProduct AffineModuleBaseChange318
open scoped ChangeOfRings
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (N : ModuleCat.{u} S)
abbrev first := (ModuleCat.extendScalars (leftMap R S S).hom).obj N
abbrev second := (ModuleCat.extendScalars (rightMap R S S).hom).obj N
abbrev comonadObject := (pullPush R S S).obj N

/-- The exact adjunction and tensor-pushout comparison convert every
original double-overlap module map into exactly one candidate coaction.
No counit or triple-overlap equation is assumed or inferred here. -/
@[expose] def homEquiv : (first R S N ⟶ second R S N) ≃
    (N ⟶ comonadObject R S N) :=
  ((ModuleCat.extendRestrictScalarsAdj (leftMap R S S).hom).homEquiv _ _).trans
    ((Iso.refl N).homCongr (component R S S N))

lemma homEquiv_apply (a : first R S N ⟶ second R S N) :
    homEquiv R S N a =
      (ModuleCat.extendRestrictScalarsAdj (leftMap R S S).hom).homEquiv _ _ a ≫
        (component R S S N).hom := by
  change (𝟙 N) ≫ _ = _
  exact Category.id_comp _

lemma homEquiv_injective : Function.Injective (homEquiv R S N) :=
  (homEquiv R S N).injective

lemma homEquiv_surjective : Function.Surjective (homEquiv R S N) :=
  (homEquiv R S N).surjective

/-- The candidate map retains the original module value of the overlap
morphism at the genuine unit tensor, followed by the actual comparison. -/
lemma homEquiv_value (a : first R S N ⟶ second R S N) (n : N) :
    homEquiv R S N a n =
      (component R S S N).hom
        (a ((1 : S ⊗[R] S) ⊗ₜ[S, (leftMap R S S).hom] n)) := by
  rw [homEquiv_apply]
  rfl
end AffineOverlapCoaction318
