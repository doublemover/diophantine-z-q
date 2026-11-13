module
public import ActualTwoDescentOriginalOverlapRationalFrameRebuild318
public section
noncomputable section
namespace ActualTwoDescentOpenAdjointSectionsRebuild318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (M : X.Modules) (N : Y.Modules)

/-- The actual adjunction unit on every ambient open, not just top. -/
def restrictSection (U : X.Opens) (s : Γ(M,U)) : Γ(M.restrict j,j ⁻¹ᵁ U) :=
  ((Scheme.Modules.restrictAdjunction j).unit.app M).app U s

lemma section_formula (U : X.Opens) (s : Γ(M,U)) :
    restrictSection j M U s=M.presheaf.map (homOfLE (j.image_preimage_le U)).op s := rfl

/-- The whole native restriction/evaluation square for every section. -/
lemma adjoint_apply (e : M.restrict j ⟶ N) (U : X.Opens) (s : Γ(M,U)) :
    ((Scheme.Modules.restrictAdjunction j).homEquiv _ _ e).app U s=
      e.app (j ⁻¹ᵁ U) (restrictSection j M U s) := by
  rw [Adjunction.homEquiv_unit]
  rfl

lemma naturality (e : M ⟶ M) (U : X.Opens) (s : Γ(M,U)) :
    restrictSection j M U (e.app U s)=
      ((Scheme.Modules.restrictFunctor j).map e).app (j ⁻¹ᵁ U)
        (restrictSection j M U s) := by
  have h := (Scheme.Modules.restrictAdjunction j).unit.naturality e
  exact congrArg (fun q => q.app U s) h
end ActualTwoDescentOpenAdjointSectionsRebuild318
