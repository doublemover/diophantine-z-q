module
public import BranchIntrinsicNaturality318
public import BranchRestrictionInjective318
public section
noncomputable section
namespace BranchSectionExtension318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 20000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev M:=FamilyIntrinsicDifferentials318.omega (ContactIntrinsicDifferentials318.structureMap c)
/-- The exact whole-common section equality, with the intrinsic module fixed
in the type so later proof composition does not unfold the naturality proof. -/
theorem naturality_eq (j:Fin 4)
    (ω:KaehlerDifferential ℚ (ContactIntrinsicFrames318.BranchRing c j)):
    (M c).presheaf.map (homOfLE (X:=(ContactGlobalSmooth318.Model c).Opens) (x:=((show Spec (CommRingCat.of (ContactKummerOrder318.OpenOrder c)) ⟶ ContactGlobalSmooth318.Model c from ContactOverlapIntrinsic318.embedding c) ''ᵁ ⊤)) (y:=ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ ⊤) (ContactFiniteTensorRestrictions318.branchLE c j)).op
      (IntrinsicChartSections318.sectionMap (Y:=ContactGlobalSmooth318.Model c) (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c j) (ContactIntrinsicFrames318.branchEmbedding c j)
        (ContactIntrinsicDifferentials318.structureMap c) (ContactIntrinsicFrames318.branch_structure c j) ω)=
    IntrinsicChartSections318.sectionMap (Y:=ContactGlobalSmooth318.Model c) (R:=ℚ) (S:=ContactKummerOrder318.OpenOrder c) (ContactOverlapIntrinsic318.embedding c)
      (ContactIntrinsicDifferentials318.structureMap c) (ContactOverlapIntrinsic318.over_Q c)
      (AlgHomDifferential318.map (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c j) (T:=ContactKummerOrder318.OpenOrder c) (ContactOverlapAlgebraMaps318.branchMap c j) ω):=
  BranchIntrinsicNaturality318.naturality c j ω
/-- A specified algebraic form on the entire branch equals the restriction
of a specified global form if their actual common-open sections agree. -/
@[expose] def section_eq (j:Fin 4) (s:Γ(M c,⊤))
    (ω:KaehlerDifferential ℚ (ContactIntrinsicFrames318.BranchRing c j))
    (h:IntrinsicChartSections318.sectionMap (Y:=ContactGlobalSmooth318.Model c) (R:=ℚ) (S:=ContactKummerOrder318.OpenOrder c) (ContactOverlapIntrinsic318.embedding c)
      (ContactIntrinsicDifferentials318.structureMap c) (ContactOverlapIntrinsic318.over_Q c)
      (AlgHomDifferential318.map (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c j) (T:=ContactKummerOrder318.OpenOrder c) (ContactOverlapAlgebraMaps318.branchMap c j) ω)=
      (M c).presheaf.map (homOfLE (X:=(ContactGlobalSmooth318.Model c).Opens) (x:=((show Spec (CommRingCat.of (ContactKummerOrder318.OpenOrder c)) ⟶ ContactGlobalSmooth318.Model c from ContactOverlapIntrinsic318.embedding c) ''ᵁ ⊤)) (show ((show Spec (CommRingCat.of (ContactKummerOrder318.OpenOrder c)) ⟶ ContactGlobalSmooth318.Model c from ContactOverlapIntrinsic318.embedding c) ''ᵁ ⊤)≤⊤ from le_top)).op s) :=
  IntegralChartSectionDetection318.global_local_eq (M c)
    (U:=ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ ⊤)
    (W:=((show Spec (CommRingCat.of (ContactKummerOrder318.OpenOrder c)) ⟶ ContactGlobalSmooth318.Model c from ContactOverlapIntrinsic318.embedding c) ''ᵁ ⊤))
    (ContactFiniteTensorRestrictions318.branchLE c j)
    (BranchRestrictionInjective318.injective c j)
    s (IntrinsicChartSections318.sectionMap (Y:=ContactGlobalSmooth318.Model c) (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c j) (ContactIntrinsicFrames318.branchEmbedding c j)
      (ContactIntrinsicDifferentials318.structureMap c) (ContactIntrinsicFrames318.branch_structure c j) ω)
    (h.symm.trans (naturality_eq c j ω).symm)
end BranchSectionExtension318
