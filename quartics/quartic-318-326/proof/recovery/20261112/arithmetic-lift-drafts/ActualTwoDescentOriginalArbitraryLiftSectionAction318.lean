module
public import ActualTwoDescentOriginalArbitraryLiftOpenAction318
public section
noncomputable section
namespace ActualTwoDescentOriginalArbitraryLiftSectionAction318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalSchemeIntegral318
open ActualTwoDescentOriginalDoublePoleSheaf318 ActualTwoDescentOriginalDoublePoleRationalEmbedding318
open ActualTwoDescentOriginalDoublePoleLocalGlobal318 ActualTwoDescentOriginalFourGenericLatticeAction318
open ActualTwoDescentSemilinearLatticeLiftGroup318
variable {K : Type*} [Field K] [CharZero K]
open ActualTwoDescentOriginalArbitraryLiftOpenAction318
lemma exists_unique (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U] (s : Γ(sheaf n,U)) :
    ∃! t : Γ(sheaf n,inverseOpen n hn a U),
      value n (inverseOpen n hn a U) t=operator (data n hn) a (value n U s) :=
  ActualTwoDescentOriginalLatticeLiftSections318.exists_unique n hn a U
    (inverseOpen n hn a U) (fun x => x.property) s
def sectionMap (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U] (s : Γ(sheaf n,U)) :
    Γ(sheaf n,inverseOpen n hn a U) := Classical.choose (exists_unique n hn a U s)
lemma value_formula (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U] (s : Γ(sheaf n,U)) :
    value n (inverseOpen n hn a U) (sectionMap n hn a U s)=operator (data n hn) a (value n U s) :=
  (Classical.choose_spec (exists_unique n hn a U s)).1
lemma additive (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U] (s t : Γ(sheaf n,U)) :
    sectionMap n hn a U (s+t)=sectionMap n hn a U s+sectionMap n hn a U t := by
  apply value_injective n (inverseOpen n hn a U)
  rw [map_add,value_formula,value_formula,value_formula,map_add,
    ActualTwoDescentSemilinearLatticeLiftCoefficients318.additive]
lemma scalar_action (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U]
    (c : Γ(originalCubicScheme n,U)) (s : Γ(sheaf n,U)) :
    sectionMap n hn a U (c • s)=
      (translation n hn a).hom.app U c • sectionMap n hn a U s := by
  apply value_injective n (inverseOpen n hn a U)
  rw [value_formula,map_smul,map_smul,value_formula]
  change operator (data n hn) a ((originalCubicScheme n).germToFunctionField U c*value n U s)=
    (originalCubicScheme n).germToFunctionField (inverseOpen n hn a U)
      ((translation n hn a).hom.app U c)*operator (data n hn) a (value n U s)
  rw [semilinear,scalar_pullback]
lemma naturality (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U V : (originalCubicScheme n).Opens) [Nonempty U] [Nonempty V] (h : V≤U)
    (s : Γ(sheaf n,U)) :
    sectionMap n hn a V ((sheaf n).presheaf.map (homOfLE h).op s)=
      (sheaf n).presheaf.map (homOfLE ((translation n hn a).hom.preimage_mono h)).op
        (sectionMap n hn a U s) := by
  apply value_injective n (inverseOpen n hn a V)
  rw [value_formula,ActualTwoDescentOriginalDoublePoleRationalEmbedding318.natural,
    ActualTwoDescentOriginalDoublePoleRationalEmbedding318.natural,value_formula]

end ActualTwoDescentOriginalArbitraryLiftSectionAction318
