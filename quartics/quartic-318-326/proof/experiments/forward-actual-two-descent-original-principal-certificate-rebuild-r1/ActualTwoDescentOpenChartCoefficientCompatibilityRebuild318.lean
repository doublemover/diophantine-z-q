module
public import ActualTwoDescentOpenChartCoefficientRebuild318
public section
noncomputable section
namespace ActualTwoDescentOpenChartCoefficientCompatibilityRebuild318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} [IsIntegral X]
  {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  (jR : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion jR]
  (jS : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion jS]
  (g : R →+* S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom g))]
  (h : Spec.map (CommRingCat.ofHom g) ≫ jR=jS)

include h in
/-- Entire native generic-stalk square of an ACTUAL affine refinement. -/
lemma comparison (z : X.functionField) :
    OpenFunctionField318.fieldEquiv jS z =
      OpenFunctionField318.fieldEquiv (Spec.map (CommRingCat.ofHom g))
        (OpenFunctionField318.fieldEquiv jR z) := by
  letI : IsDominant jR :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace jR jR.isOpenEmbedding.isOpenMap⟩
  let f := Spec.map (CommRingCat.ofHom g)
  letI : IsDominant f :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace f f.isOpenEmbedding.isOpenMap⟩
  have he := DominantFunctionField318.map_comp f jR
  have hf : f ≫ jR=jS := h
  rw [hf] at he
  simpa only [DominantFunctionField318.map_open] using
    congrArg (fun k => k z) he

include h in
lemma coefficient (r : R) :
    ActualTwoDescentOpenChartCoefficientRebuild318.coefficient jR r =
      ActualTwoDescentOpenChartCoefficientRebuild318.coefficient jS (g r) := by
  let f := Spec.map (CommRingCat.ofHom g)
  letI : IsDominant f :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace f f.isOpenEmbedding.isOpenMap⟩
  apply (OpenFunctionField318.fieldEquiv jS).injective
  rw [comparison jR jS g h,
    ActualTwoDescentOpenChartCoefficientRebuild318.comparison,
    ActualTwoDescentOpenChartCoefficientRebuild318.comparison]
  exact AffineFunctionFieldMap318.on_coefficient g r
end ActualTwoDescentOpenChartCoefficientCompatibilityRebuild318
