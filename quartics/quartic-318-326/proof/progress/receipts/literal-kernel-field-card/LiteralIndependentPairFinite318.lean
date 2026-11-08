module
public import LiteralIndependentPairFunctor318
public import LiteralKernelFiniteEtale318
public section
noncomputable section
namespace LiteralIndependentPairFinite318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
@[expose] def structureMap : LiteralIndependentPairOpen318.scheme N ⟶
    Spec (CommRingCat.of (OpenJModel318.Base N)):=
  LiteralIndependentPairOpen318.inclusion N ≫ LiteralKernelAddition318.productBase N
/-- The actual independent-pair locus is finite and etale over the literal
base. Surjectivity and numerical rank are not inferred here. -/
theorem finite_etale : IsFinite (structureMap N) ∧ Etale (structureMap N):=by
  haveI:IsFinite (LiteralKernelSchemePoints318.structureMap N):=
    (LiteralKernelFiniteEtale318.finite_etale N).1
  haveI:Etale (LiteralKernelSchemePoints318.structureMap N):=
    (LiteralKernelFiniteEtale318.finite_etale N).2
  dsimp only [structureMap,LiteralKernelAddition318.productBase]
  exact ⟨inferInstance,inferInstance⟩
end LiteralIndependentPairFinite318
