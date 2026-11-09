module
public import ProjectiveLinePointEquiv318
public import SphereInversion318
public import Mathlib.Topology.Constructions.SumProd
public section
noncomputable section
open Function Filter Topology
namespace ProjectiveLineComplexTopology318
open ProjectiveLineFieldPoints318 ProjectiveLinePointEquiv318 SphereInversion318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev ComplexPoints := Points (R:=ℚ) (K:=ℂ)

/-- The two actual polynomial-evaluation charts of the arithmetic projective line. -/
@[expose] def algebraicChartCover : ℂ ⊕ ℂ → ComplexPoints :=
  Sum.elim (chartPoint (R:=ℚ) 1) (chartPoint (R:=ℚ) 0)

/-- The ordinary complex chart topology on the actual scheme-valued points.
This definition uses only the two original algebraic evaluation maps. -/
@[expose,instance_reducible] def complexPointTopology : TopologicalSpace ComplexPoints :=
  TopologicalSpace.coinduced algebraicChartCover inferInstance

@[expose] def sphereCover : ℂ ⊕ ℂ → OnePoint ℂ :=
  Sum.elim ((↑) : ℂ → OnePoint ℂ) (fun t => inversion (t : OnePoint ℂ))

lemma sphereCover_continuous : Continuous sphereCover :=
  continuous_sum_dom.mpr ⟨OnePoint.continuous_coe,
    inversion_continuous.comp OnePoint.continuous_coe⟩

lemma sphereCover_open : IsOpenMap sphereCover :=
  isOpenMap_sumElim.mpr ⟨OnePoint.isOpenEmbedding_coe.isOpenMap,
    inversionHomeomorph.isOpenMap.comp OnePoint.isOpenEmbedding_coe.isOpenMap⟩

lemma sphereCover_surjective : Function.Surjective sphereCover := by
  intro z
  induction z using OnePoint.rec with
  | infty => exact ⟨Sum.inr 0,inversion_zero⟩
  | coe t => exact ⟨Sum.inl t,rfl⟩

lemma sphereCover_quotient : IsQuotientMap sphereCover :=
  sphereCover_open.isQuotientMap sphereCover_continuous sphereCover_surjective

lemma pointMap_inversion (t : ℂ) :
    pointMap (R:=ℚ) (inversion (t : OnePoint ℂ))=chartPoint (R:=ℚ) 0 t := by
  by_cases ht : t=0
  · subst t
    rw [inversion_zero]
    rfl
  · rw [inversion_coe ht]
    change chartPoint (R:=ℚ) 1 t⁻¹=chartPoint (R:=ℚ) 0 t
    simpa only [Units.val_inv_eq_inv_val,Units.val_mk0,inv_inv] using
      unit_overlap (R:=ℚ) (Units.mk0 t ht)⁻¹

lemma pointMap_sphereCover : pointMap (R:=ℚ) ∘ sphereCover=algebraicChartCover := by
  funext z
  cases z with
  | inl t => rfl
  | inr t => exact pointMap_inversion t

lemma pointMap_continuous :
    letI := complexPointTopology
    Continuous (pointMap (R:=ℚ) (K:=ℂ)) := by
  let := complexPointTopology
  apply sphereCover_quotient.continuous_iff.mpr
  rw [pointMap_sphereCover]
  exact continuous_coinduced_rng

lemma inverse_finite (t : ℂ) :
    (pointEquiv (R:=ℚ)).symm (chartPoint (R:=ℚ) 1 t)=(t : OnePoint ℂ) :=
  (pointEquiv (R:=ℚ)).symm_apply_apply (t : OnePoint ℂ)

lemma inverse_reciprocal (t : ℂ) :
    (pointEquiv (R:=ℚ)).symm (chartPoint (R:=ℚ) 0 t)=inversion (t : OnePoint ℂ) := by
  apply (pointEquiv (R:=ℚ)).injective
  rw [Equiv.apply_symm_apply]
  exact (pointMap_inversion t).symm

lemma pointEquiv_symm_continuous :
    letI := complexPointTopology
    Continuous (pointEquiv (R:=ℚ) (K:=ℂ)).symm := by
  let := complexPointTopology
  apply continuous_coinduced_dom.mpr
  apply continuous_sum_dom.mpr
  constructor
  · simpa only [Function.comp_def,algebraicChartCover,Sum.elim_inl,inverse_finite] using
      OnePoint.continuous_coe (X:=ℂ)
  · simpa only [Function.comp_def,algebraicChartCover,Sum.elim_inr,inverse_reciprocal] using
      inversion_continuous.comp (OnePoint.continuous_coe (X:=ℂ))

/-- The independent standard sphere is homeomorphic to the actual complex-valued
points of the original arithmetic Proj with its original two-chart topology. -/
@[expose] def pointHomeomorph :
    letI := complexPointTopology
    OnePoint ℂ ≃ₜ ComplexPoints :=
  { pointEquiv with
    continuous_toFun := pointMap_continuous
    continuous_invFun := pointEquiv_symm_continuous }

end ProjectiveLineComplexTopology318
