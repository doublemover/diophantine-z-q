module
public import FifthFormAffineRestriction318
public section
noncomputable section
namespace FifthFormCommonOpen318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthFormLocalCoefficients318 ContactOverlapIntrinsic318
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] toOpen_open
theorem global_restrict (i:Fin 4):M.presheaf.map (homOfLE (show
    embedding units ''ᵁ ⊤≤⊤ from le_top)).op (ContactCharacterDifferentials318.differential i)=
    IntrinsicChartSections318.sectionMap (embedding units)
      (ContactIntrinsicDifferentials318.structureMap units) (over_Q units) (form i):=by
  let res : Γ(M,SourceGlobalAffine318.chartEmbedding units ''ᵁ ⊤) →
      Γ(M,embedding units ''ᵁ ⊤) := M.presheaf.map (homOfLE sourceLE).op
  have h1:=congrArg res (ContactCharacterAffinePullback318.finite_restrict i)
  have h2:=CategoryTheory.Functor.map_comp_apply M.presheaf
    (homOfLE (show SourceGlobalAffine318.chartEmbedding units ''ᵁ ⊤≤⊤ from le_top)).op
    (homOfLE sourceLE).op (ContactCharacterDifferentials318.differential i)
  exact h2.trans (h1.symm.trans (affine_restrict i))

end FifthFormCommonOpen318
