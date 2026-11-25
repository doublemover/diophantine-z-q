module

public import OriginalRetainedComplexPointFromE318
public import OriginalLiteralMarkedRealPeriodColumns318
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section
noncomputable section

namespace OriginalRetainedFullPeriodSpan318

open AlgebraicGeometry CategoryTheory Topology
open OriginalRetainedComplexZeroByPasting318 OriginalLiteralMarkedRealPeriodColumns318
open scoped CategoryTheory.Obj CategoryTheory.MonObj BigOperators
attribute [local instance] Over.cartesianMonoidalCategory

/-- Grouped ambient real coordinates are the strict R122 elementary
coordinate equivalence, before any period basis or lattice matching. -/
theorem dual_continuous (l : C2 →ₗ[ℝ] ℝ) : Continuous l := by
  let b := Pi.basisFun ℝ (Fin 4)
  let W := groupedCoordinates.symm.toLinearEquiv
  have read (z : C2) : (∑ i : Fin 4, groupedCoordinates z i * l (W (b i))) = l z := by
    have h := congrArg (fun t => l (W t)) (b.sum_repr (groupedCoordinates z))
    simpa [b,W,Pi.basisFun_repr,map_sum,map_smul,smul_eq_mul] using h
  have h : Continuous (fun z : C2 => ∑ i : Fin 4, groupedCoordinates z i * l (W (b i))) :=
    continuous_finsetSum _ (fun i _ => ((continuous_apply i).comp groupedCoordinates.continuous).mul_const _)
  rw [show (fun z : C2 => ∑ i : Fin 4, groupedCoordinates z i * l (W (b i))) = l from funext read] at h
  exact h

variable {A Y E : Scheme} (a : A ⟶ Y) [GrpObj (Over.mk a)] (P33 : E ⟶ Y)
local notation "T" => Spec (CommRingCat.of ℂ)
variable (σ : T ⟶ E)
local notation "F" => fiber a (σ≫P33)
local notation "G" => Additive (Over.mk (𝟙 T) ⟶ F)
variable (q : C2 →+ G)

theorem discrete_actual_kernel (U : Set C2) (hU : IsOpen U) (zeroU : (0 : C2) ∈ U)
    (near : Set.InjOn q U) : DiscreteTopology q.ker := by
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  refine ⟨U,hU,?_⟩
  ext x
  change (x.val ∈ U) ↔ x=0
  constructor
  · intro h
    apply Subtype.ext
    apply near h zeroU
    exact x.property.trans q.map_zero.symm
  · rintro rfl
    exact zeroU

variable [TopologicalSpace G] [CompactSpace G] (quot : IsQuotientMap q)

include quot in
/-- The WHOLE kernel of the one original q spans its real tangent.
It is not enough that four candidate columns are independent.
Separate compactness of the actual original point topology and open
surjectivity of q can supply precisely the inputs here. -/
theorem whole_kernel_spans : Submodule.span ℝ (q.ker : Set C2) = ⊤ := by
  let L := Submodule.span ℝ (q.ker : Set C2)
  by_contra hL
  obtain ⟨z,hz⟩ := SetLike.exists_notMem_of_ne_top L hL rfl
  obtain ⟨l,hl,hmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
  have vanishes (v : C2) (hv : v ∈ q.ker) : l v=0 := by
    have hh : l v ∈ L.map l := Submodule.mem_map.2 ⟨v,Submodule.subset_span hv,rfl⟩
    rw [hmap] at hh
    exact Submodule.mem_bot.1 hh
  let x (p : G) := (quot.surjective p).choose
  have preimage (p : G) : q (x p)=p := (quot.surjective p).choose_spec
  let aℝ (p : G) := l (x p)
  have read (v : C2) : aℝ (q v)=l v := by
    have h : x (q v)-v ∈ q.ker := by
      change q (x (q v)-v)=0
      rw [map_sub,preimage,sub_self]
    have h₀ := vanishes _ h
    rw [map_sub,sub_eq_zero] at h₀
    exact h₀
  have ha : Continuous aℝ :=
    quot.continuous_iff.2 (by
      rw [show aℝ ∘ q = l from funext read]
      exact dual_continuous l)
  have onto : Function.Surjective aℝ := by
    intro t
    refine ⟨q ((t/(l z)) • z),?_⟩
    rw [read,map_smul,smul_eq_mul,div_mul_cancel₀ _ hl]
  have hb : BddAbove (Set.univ : Set ℝ) := by
    rw [← onto.range_eq]
    exact (isCompact_range ha).bddAbove
  obtain ⟨B,hB⟩ := hb
  exact (not_lt_of_ge (hB (Set.mem_univ (B+1)))) (lt_add_one B)

end OriginalRetainedFullPeriodSpan318
