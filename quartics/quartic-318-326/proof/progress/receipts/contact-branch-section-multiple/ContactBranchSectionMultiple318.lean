module
public import ContactBranchRepresentation318
public import IntrinsicChartLocalMultiple318
public section
noncomputable section
namespace ContactBranchSectionMultiple318
open AlgebraicGeometry CategoryTheory Opposite ContactBranchRepresentation318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ) (i:Fin 4)
/-- The canonical whole-branch representative and a supplied original chart
presentation give a whole-branch regular scalar multiple of the unchanged
actual global sections. All twists and both sections remain abstract. -/
@[expose] def section_multiple (s t:Γ(M c,⊤)) (w:KaehlerDifferential ℚ (B c i))
    (ht:IntrinsicChartSections318.sectionMap (j c i) (p c) (ContactIntrinsicFrames318.branch_structure c i) w=
      (M c).presheaf.map (homOfLE (show j c i ''ᵁ ⊤≤(⊤:(X c).Opens) from le_top)).op t)
    (h:∃a:B c i,representation c i s=a • w):=
  IntrinsicChartLocalMultiple318.section_multiple (X:=X c) (R:=ℚ) (S:=B c i)
    (p c) (j c i) (ContactIntrinsicFrames318.branch_structure c i) s t w ht h
end ContactBranchSectionMultiple318
