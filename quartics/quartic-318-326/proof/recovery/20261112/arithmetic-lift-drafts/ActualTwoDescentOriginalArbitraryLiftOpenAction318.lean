module
public import ActualTwoDescentOriginalConstantKernelEquivalence318
public section
noncomputable section
namespace ActualTwoDescentOriginalArbitraryLiftOpenAction318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalSchemeIntegral318
open ActualTwoDescentOriginalDoublePoleSheaf318 ActualTwoDescentOriginalDoublePoleRationalEmbedding318
open ActualTwoDescentOriginalDoublePoleLocalGlobal318 ActualTwoDescentOriginalFourGenericLatticeAction318
open ActualTwoDescentSemilinearLatticeLiftGroup318
variable {K : Type*} [Field K] [CharZero K]
abbrev translation (n : K) (hn : n≠0) (a : Lift (data n hn)) :=
  ActualTwoDescentOriginalFourSchemeTranslations318.iso n hn (projection (data n hn) a).toAdd
abbrev inverseOpen (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) := (translation n hn a).hom ⁻¹ᵁ U
instance inverse_nonempty (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U] : Nonempty (inverseOpen n hn a U) :=
  ActualTwoDescentIntegralGenericSectionMaps318.preimage_nonempty _ U
lemma sigma_native (n : K) (hn : n≠0) (a : Lift (data n hn)) (f : SchemeFunctionField n) :
    (data n hn).sigma (projection (data n hn) a) f=
      ActualTwoDescentOpenImmersionGenericStalk318.genericFieldEquiv (translation n hn a).hom f := by
  change sigma n hn (projection (data n hn) a).toAdd f=_
  unfold sigma translation ActualTwoDescentOriginalFourSchemeTranslations318.iso
  cases ActualTwoDescentOriginalFourSchemeTranslations318.index (projection (data n hn) a).toAdd with
  | none => exact (ActualTwoDescentGenericAutomorphismFractionalLines318.generic_identity f).symm
  | some i => rfl
lemma scalar_pullback (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U] (c : Γ(originalCubicScheme n,U)) :
    (data n hn).sigma (projection (data n hn) a) ((originalCubicScheme n).germToFunctionField U c)=
      (originalCubicScheme n).germToFunctionField (inverseOpen n hn a U)
        ((translation n hn a).hom.app U c) := by
  rw [sigma_native]
  exact ActualTwoDescentIntegralGenericSectionMaps318.actual_generic_section_pullback _ U c

end ActualTwoDescentOriginalArbitraryLiftOpenAction318
