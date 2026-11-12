module
public import SectionGeneratedGluing318
public section
noncomputable section
namespace RestrictedMapBijective318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)

/-- A genuine restricted sheaf isomorphism is bijective on every ambient
subopen of its actual image. -/
theorem bijective [IsIso ((Scheme.Modules.restrictFunctor j).map f)]
    (V : X.Opens) (hV : V≤j ''ᵁ ⊤) : Function.Bijective (f.app V) := by
  let P (V : X.Opens) := Function.Bijective (f.app V)
  have hchart (U : Y.Opens) : P (j ''ᵁ U) :=
    ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.restrictFunctor j).map f).app U)
  have he : j ''ᵁ (j⁻¹ᵁ V)=V := by
    apply TopologicalSpace.Opens.ext
    apply Set.image_preimage_eq_of_subset
    intro x hx
    obtain ⟨y,_,hy⟩ := hV hx
    exact ⟨y,hy⟩
  exact Eq.mp (congrArg P he) (hchart (j⁻¹ᵁ V))
end RestrictedMapBijective318
