module

public import OriginalRetainedF33ExponentialQuotient318
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Positivity

@[expose] public section
noncomputable section

namespace OriginalRetainedActualKernelFiniteIndex318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedF33ExponentialQuotient318
open scoped Topology

variable {A Y : Scheme} (a : A ⟶ Y) [GrpObj (Over.mk a)]
variable {E : Type} [Field E] (σ : E→+*ℂ)
variable (P33 : Spec (CommRingCat.of E) ⟶ Y)
local notation "G" => Additive (Points a σ P33)

variable (q : Tangent→+G)
local notation "K" => q.ker
abbrev R4 := Fin 4→ℝ

variable (basisRead : R4 ≃L[ℝ] Tangent)
variable (per : IntegralLabels →+ K)
variable (matches : ∀ n : IntegralLabels, (per n).val=basisRead (fun i => (n i : ℝ)))

def fundamentalClosedBox : Set Tangent :=
  basisRead '' Set.Icc (0:R4) (1:R4)

theorem fundamentalClosedBox_compact : IsCompact (fundamentalClosedBox basisRead) :=
  isCompact_Icc.image basisRead.continuous

variable [ProperSpace Tangent] [DiscreteTopology K]

theorem finite_interval_representatives (closed : IsClosed (K : Set Tangent)) :
    Finite {z : K // z.val∈fundamentalClosedBox basisRead} := by
  have inter : (fundamentalClosedBox basisRead ∩ (K : Set Tangent)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (fundamentalClosedBox_compact basisRead).isBounded closed
  letI := inter.fintype
  exact Finite.of_injective
    (fun z : {z : K // z.val∈fundamentalClosedBox basisRead} =>
      (⟨z.val.val,z.property,z.val.property⟩ :
        fundamentalClosedBox basisRead ∩ (K : Set Tangent)))
    (fun x y h => Subtype.ext (Subtype.ext (congrArg Subtype.val h)))

include matches in
theorem subtract_primitive_integer_part (z : K) :
    ∃ n : IntegralLabels, (z-per n).val∈fundamentalClosedBox basisRead := by
  let r := basisRead.symm z.val
  let n : IntegralLabels := fun i => ⌊r i⌋
  let t : R4 := fun i => Int.fract (r i)
  have lower : (0:R4)≤t := fun i => Int.fract_nonneg (r i)
  have upper : t≤(1:R4) := fun i => (Int.fract_lt_one (r i)).le
  have ht : t=r-(fun i => (n i:ℝ)) := rfl
  refine ⟨n,t,⟨lower,upper⟩,?_⟩
  change basisRead t=z.val-(per n).val
  rw [ht,map_sub,basisRead.apply_symm_apply,matches n]

include matches in
/-- Finite index is proved inside the *whole* kernel of the one actual
q, not by treating a real determinant as an integral basis proof. The
candidate here can be any four independent actual periods; the final
quaternion label identification still uses the actual polarization. -/
theorem actual_kernel_integer_span_finite_index (closed : IsClosed (K : Set Tangent)) :
    Finite (K ⧸ per.range) := by
  letI := finite_interval_representatives a σ P33 q basisRead closed
  let m := QuotientAddGroup.mk' per.range
  apply Finite.of_surjective (fun z : {z : K // z.val∈fundamentalClosedBox basisRead} => m z.val)
  intro v
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective (N:=per.range) v
  obtain ⟨n,hn⟩ := subtract_primitive_integer_part a σ P33 q basisRead per matches z
  refine ⟨⟨z-per n,hn⟩,?_⟩
  change m (z-per n)=m z
  have zero : m (per n)=0 := (QuotientAddGroup.eq_zero_iff (N:=per.range) _).2 ⟨n,rfl⟩
  rw [map_sub,zero,sub_zero]

include matches in
theorem exact_uniform_denominator_of_actual_periods (closed : IsClosed (K : Set Tangent)) :
    ∃ N : ℕ, 0<N ∧ ∀ z : K, ∃ n : IntegralLabels, N • z=per n := by
  letI := actual_kernel_integer_span_finite_index a σ P33 q basisRead per matches closed
  let N := Nat.card (K ⧸ per.range)
  have hN : 0<N := Nat.card_pos
  refine ⟨N,hN,?_⟩
  intro z
  let m := QuotientAddGroup.mk' per.range
  have hm : m (N • z)=0 := by
    rw [map_nsmul]
    exact card_nsmul_eq_zero'
  exact (QuotientAddGroup.eq_zero_iff (N:=per.range) _).1 hm

end OriginalRetainedActualKernelFiniteIndex318
