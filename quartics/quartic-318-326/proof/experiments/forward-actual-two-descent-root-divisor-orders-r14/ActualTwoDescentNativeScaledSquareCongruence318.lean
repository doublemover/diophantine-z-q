module
public import ActualTwoDescentNativeScaledSquareRestriction318
public section
noncomputable section
namespace ActualTwoDescentNativeScaledSquareCongruence318
open CategoryTheory AlgebraicGeometry Opposite
open ActualTwoDescentNativeScaledSquareRestriction318
universe u
variable {X Y : Scheme.{u}}

lemma restriction_congr_refl (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) :
    (Scheme.Modules.restrictFunctorCongr (rfl : j=j)).inv.app M=𝟙 (M.restrict j) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change M.presheaf.map (𝟙 (op (j ''ᵁ U))) s=s
  simp only [Functor.map_id]

/-- Equality of ambient embeddings is not erased from the comparison:
the native source transport acts on both tensor factors by the same map. -/
lemma squareMap_congr {j j' : Y ⟶ X} (h : j=j')
    [IsOpenImmersion j] [IsOpenImmersion j'] (M : X.Modules)
    (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf) (a : Γ(Y,⊤)) :
    (Scheme.Modules.restrictFunctorCongr h).inv.app (IntrinsicTensorSheaf318.tensor M M) ≫
      squareMap j M f a=
    squareMap j' M ((Scheme.Modules.restrictFunctorCongr h).inv.app M ≫ f) a := by
  cases h
  rw [restriction_congr_refl,restriction_congr_refl,Category.id_comp,Category.id_comp]
end ActualTwoDescentNativeScaledSquareCongruence318
