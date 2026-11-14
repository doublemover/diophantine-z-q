module
public import ModuleFrameDescent318
public section
noncomputable section
namespace OpenImmersionModuleIsoCriterion318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)

/-- The literal map on any ambient subopen of an open immersion's range is
an isomorphism when its restriction is; the actual scalar map is retained. -/
lemma app_isIso {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    [IsIso ((Scheme.Modules.restrictFunctor j).map f)]
    (V : X.Opens) (hV : V ≤ j.opensRange) : IsIso (f.app V) := by
  have hi : IsIso (((Scheme.Modules.restrictFunctor j).map f).app (j ⁻¹ᵁ V)) :=
    inferInstance
  change IsIso (f.app (j ''ᵁ (j ⁻¹ᵁ V))) at hi
  have he : j ''ᵁ (j ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,inf_eq_right.mpr hV]
  exact (congrArg (fun O => IsIso (f.app O)) he).mp hi

/-- Descent for the SAME map on an arbitrary covering family of open
immersions, without replacing the chart schemes by chosen points. -/
lemma of_cover {ι : Type u} (Y : ι → Scheme.{u}) (j : ∀ i,Y i ⟶ X)
    [∀ i,IsOpenImmersion (j i)] (hc : (⊤ : X.Opens) ≤ ⨆ i,(j i).opensRange)
    (hf : ∀ i,IsIso ((Scheme.Modules.restrictFunctor (j i)).map f)) : IsIso f := by
  apply ModuleFrameDescent318.isIso_of_cover (fun i => (j i).opensRange) hc
  intro i V hV
  letI := hf i
  exact app_isIso f (j i) V hV
end OpenImmersionModuleIsoCriterion318
