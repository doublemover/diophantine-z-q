module
public import ModuleTopExt318
public section
noncomputable section
namespace SectionGeneratorIsomorphism318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (s : Γ(M,⊤))

/-- Generation on every ambient subopen proves the literal restriction of
its section morphism is an isomorphism of sheaves, not only on top sections. -/
theorem restrict_isIso (hs : ∀ (V : X.Opens), V≤j ''ᵁ ⊤ →
    Function.Bijective (fun a : Γ(X,V) => a •
      M.presheaf.map (homOfLE (show V≤⊤ from le_top)).op s)) :
    IsIso ((Scheme.Modules.restrictFunctor j).map (ModuleGlobalSections318.ofTop M s)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun a : Γ(X,j ''ᵁ U) =>
    (ModuleGlobalSections318.ofTop M s).val.app (op (j ''ᵁ U)) a)
  simpa only [ModuleGlobalSections318.ofTop_apply] using hs (j ''ᵁ U) (j.image_mono le_top)
end SectionGeneratorIsomorphism318
