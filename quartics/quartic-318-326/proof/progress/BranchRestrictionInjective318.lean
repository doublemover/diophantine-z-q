module
public import BranchIntrinsicNaturality318
public import IntegralChartSectionDetection318
public section
noncomputable section
namespace BranchRestrictionInjective318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 20000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
variable (c:Fin 4→ℚˣ)
theorem injective (j:Fin 4):Function.Injective
    ((ContactIntrinsicDifferentials318.omega c).presheaf.map
      (homOfLE (X:=(ContactGlobalSmooth318.Model c).Opens) (x:=((show Spec (CommRingCat.of (ContactKummerOrder318.OpenOrder c)) ⟶ ContactGlobalSmooth318.Model c from ContactOverlapIntrinsic318.embedding c) ''ᵁ ⊤)) (y:=ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ ⊤) (ContactFiniteTensorRestrictions318.branchLE c j)).op):=by
  letI:IsIntegral (ContactGlobalSmooth318.Model c):=
    (ContactGlobalSmooth318.smooth_proper_integral_model c).2.2
  letI : Nonempty (((show Spec (CommRingCat.of (ContactKummerOrder318.OpenOrder c)) ⟶ ContactGlobalSmooth318.Model c from ContactOverlapIntrinsic318.embedding c) ''ᵁ ⊤)) :=
    ContactGlobalSectionDetection318.common_nonempty c
  exact IntegralChartSectionDetection318.restrict_injective
    (ContactIntrinsicDifferentials318.omega c)
    (ContactIntrinsicFrames318.branchEmbedding c j) (ContactIntrinsicFrames318.branchFrame c j)
    ((show Spec (CommRingCat.of (ContactKummerOrder318.OpenOrder c)) ⟶ ContactGlobalSmooth318.Model c from ContactOverlapIntrinsic318.embedding c) ''ᵁ ⊤) (ContactFiniteTensorRestrictions318.branchLE c j)
end BranchRestrictionInjective318
