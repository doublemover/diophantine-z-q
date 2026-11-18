module
public import FourRootProjectiveFiniteDescent318
public import ActualOpenFractionField318
public import Mathlib.FieldTheory.RatFunc.Basic
public section
noncomputable section
namespace ActualComplexProjectiveFunctionField318
open AlgebraicGeometry CategoryTheory Set TopologicalSpace
abbrev Y:=ProjectiveJLine318.scheme ℂ
abbrev P:=Polynomial ℂ
abbrev K:=RatFunc ℂ

lemma chart_intersection:
    ((JLineAtlas318.chart ℂ 0).opensRange⊓(JLineAtlas318.chart ℂ 1).opensRange:Y.Opens)≠⊥:=by
  let p:PrimeSpectrum P:=⟨⊥,Ideal.isPrime_bot⟩
  have hp:p∈PrimeSpectrum.basicOpen (Polynomial.X:P):=Polynomial.X_ne_zero
  have hp1:JLineAtlas318.chart ℂ 0 p∈(JLineAtlas318.chart ℂ 1).opensRange:=by
    change p∈JLineAtlas318.chart ℂ 0 ⁻¹ᵁ(JLineAtlas318.chart ℂ 1).opensRange
    rw [ProjectiveLineComplexChartGeometry318.chart_zero_preimage_one]
    exact hp
  intro h
  have he:JLineAtlas318.chart ℂ 0 p∈
      ((JLineAtlas318.chart ℂ 0).opensRange⊓(JLineAtlas318.chart ℂ 1).opensRange):=
    ⟨⟨p,rfl⟩,hp1⟩
  rw [h] at he
  exact he

instance irreducible:IrreducibleSpace Y:=by
  let U:Fin 2→Y.Opens:=fun j=>(JLineAtlas318.chart ℂ j).opensRange
  have hi:∀j,IsPreirreducible (U j:Set Y):=by
    intro j
    simpa [U,Set.image_univ] using
      (PreirreducibleSpace.isPreirreducible_univ (X:=Spec (CommRingCat.of P))).image
        (JLineAtlas318.chart ℂ j) (JLineAtlas318.chart ℂ j).continuous.continuousOn
  have hn:Pairwise (fun i j=>¬Disjoint (U i) (U j)):=by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [U,disjoint_iff] using chart_intersection
    · simpa [U,disjoint_iff,inf_comm] using chart_intersection
    · exact (hij rfl).elim
  have hu:(Set.univ:Set Y)⊆⋃j:Fin 2,(U j:Set Y):=by
    intro p _
    obtain ⟨j,q,hq⟩:=FourRootProjectiveFiniteDescent318.targetCover.exists_eq p
    exact mem_iUnion.mpr ⟨j,q,hq⟩
  rw [irreducibleSpace_def]
  exact ⟨⟨JLineAtlas318.chart ℂ 0 (Classical.choice inferInstance),mem_univ _⟩,
    IsPreirreducible.of_subset_iUnion hn hi isOpen_univ hu⟩
instance reduced:IsReduced Y:=by
  haveI:∀j,IsReduced (FourRootProjectiveFiniteDescent318.targetCover.X j):=by
    intro j
    change IsReduced (Spec (CommRingCat.of P))
    infer_instance
  exact IsReduced.of_openCover _ FourRootProjectiveFiniteDescent318.targetCover
instance integral:IsIntegral Y:=isIntegral_of_irreducibleSpace_of_isReduced _
instance chartDominant (j:Fin 2):IsDominant (JLineAtlas318.chart ℂ j):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (JLineAtlas318.chart ℂ j).isOpenEmbedding.isOpenMap⟩

@[expose,instance_reducible] def affineAlgebra:Algebra P Y.functionField:=
  ActualOpenFractionField318.sourceAlgebra (JLineAtlas318.chart ℂ 1)
attribute [local instance] affineAlgebra
local instance projectiveFraction:IsFractionRing P Y.functionField:=
  ActualOpenFractionField318.fractionRing (JLineAtlas318.chart ℂ 1)
/-- Actual complex Proj function field, through its original finite
chart1 coordinate t. The rational-base theorem over Q is not substituted. -/
@[expose] def comparison:Y.functionField≃ₐ[P]K:=
  ActualOpenFractionField318.equiv (JLineAtlas318.chart ℂ 1) K
lemma on_polynomial (p:P):comparison (algebraMap P Y.functionField p)=algebraMap P K p:=
  comparison.commutes p
end ActualComplexProjectiveFunctionField318
