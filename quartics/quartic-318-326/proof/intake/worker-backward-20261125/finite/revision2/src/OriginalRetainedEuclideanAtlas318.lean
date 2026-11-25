module

public import OriginalRetainedAffineChartTransitions318
import Mathlib.Data.Finset.Max

@[expose] public section
noncomputable section

namespace OriginalRetainedEuclideanAtlas318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedProjectiveAffinePoints318 OriginalRetainedComplexZeroByPasting318
open OriginalRetainedProjectiveRatio318 OriginalRetainedAffineChartPointEquiv318
open OriginalRetainedAffineChartTransitions318

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "X" => retainedCarrier a P33 σ
local notation "F" => fiber a (σ≫P33)
local notation "P" => (Over.mk (𝟙 T) ⟶ F)
variable (embedding : X ⟶ Ambient κ) (C : ∀ i, Chart a P33 σ embedding i)
local notation "rows" => (fun i => Rows (C i).I)
local notation "addr" => (fun i => OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding (C i))

/-- Took every chart from the one original closed projective embedding. -/
def originalCharts [IsClosedImmersion embedding]
    (h : embedding≫projectiveBase κ=retainedBase a P33 σ) :
    ∀ i, Chart a P33 σ embedding i :=
  fun i => OriginalRetainedClosedProjectiveEvaluation318.choose a P33 σ embedding h i

theorem addr_in_chart (i : κ) (z : rows i) : Set.range (addr i z).left ⊆ Set.range (C i).j :=
  (liftRow a P33 σ embedding (C i) z).property

theorem addr_injective (i : κ) : Function.Injective (addr i) := by
  intro r s h
  apply (chartEquiv a P33 σ embedding (C i)).injective
  exact Subtype.ext h

def address (z : Sigma rows) : P := addr z.1 z.2

theorem all_points_addressed : Function.Surjective (address a P33 σ embedding C) := by
  intro p
  obtain ⟨i,q,hq⟩ := actual_point_factors_piece κ a P33 σ embedding p.left
  have hi : Set.range p.left ⊆ Set.range (C i).j := by
    rw [(C i).rangeChart]
    rintro _ ⟨u,rfl⟩
    refine ⟨q u,?_⟩
    exact congrArg (fun f : T ⟶ X => f u) hq
  let q₀ : PointsInPiece (C i).I a P33 σ (C i).j := ⟨p,hi⟩
  refine ⟨⟨i,(chartEquiv a P33 σ embedding (C i)).symm q₀⟩,?_⟩
  exact congrArg Subtype.val ((chartEquiv a P33 σ embedding (C i)).apply_symm_apply q₀)

/-- The topology is on the exact set of based Spec(C) arrows of
the original E-fibre. It is not the scheme Zariski topology. -/
def euclidean : TopologicalSpace P :=
  TopologicalSpace.coinduced (address a P33 σ embedding C) inferInstance

local instance chosenTopology : TopologicalSpace P := euclidean a P33 σ embedding C

theorem open_iff (U : Set P) : IsOpen U ↔ ∀ i, IsOpen (addr i ⁻¹' U) :=
  isOpen_coinduced.trans isOpen_sigma_iff

theorem addr_continuous (i : κ) : Continuous (addr i) :=
  (continuous_coinduced_rng (f:=address a P33 σ embedding C)).comp continuous_sigmaMk

theorem addr_open (k : κ) : IsOpenMap (addr k) := by
  intro U hU
  apply (open_iff a P33 σ embedding C _).2
  intro i
  let f := transition a P33 σ embedding (C i) (C k)
  let V := Overlap (k:=k) a P33 σ embedding (C i)
  have eq : addr i ⁻¹' (addr k '' U) = (Subtype.val : V → rows i) '' (f ⁻¹' U) := by
    ext r
    constructor
    · rintro ⟨w,hw,e⟩
      have nz := (chart_domain a P33 σ embedding (C i) (C k) r).1
        (e ▸ addr_in_chart a P33 σ embedding C k w)
      let v : V := ⟨r,nz⟩
      have h := same_point a P33 σ embedding (C i) (C k) v
      have e' : w=f v := addr_injective a P33 σ embedding C k (e.trans h.symm)
      exact ⟨v,e' ▸ hw,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨f v,hv,same_point a P33 σ embedding (C i) (C k) v⟩
  rw [eq]
  exact (overlap_open (k:=k) a P33 σ embedding (C i)).isOpenMap_subtype_val _
    (hU.preimage (transition_continuous a P33 σ embedding (C i) (C k)))

/-- On the actual Euclidean topology every literal quotient chart
is a genuine open embedding; it keeps the R242 two inverse maps. -/
theorem chart_open_embedding (i : κ) : Topology.IsOpenEmbedding (addr i) :=
  .of_continuous_injective_isOpenMap (addr_continuous a P33 σ embedding C i)
    (addr_injective a P33 σ embedding C i) (addr_open a P33 σ embedding C i)

def dominant (i : κ) : Set (rows i) :=
  Subtype.val ⁻¹' Metric.closedBall (0 : {j : κ // j≠i} → ℂ) 1

theorem dominant_compact (i : κ) : IsCompact (dominant a P33 σ embedding C i) := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  rw [dominant, Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_comm]
  exact compact_slice (C i).I

theorem dominant_cover :
    (⋃ i : κ, addr i '' dominant a P33 σ embedding C i) = (Set.univ : Set P) := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro p _
  obtain ⟨⟨i,r⟩,hr⟩ := all_points_addressed a P33 σ embedding C p
  change addr i r=p at hr
  let v := promote r.val
  have h₀ : (Finset.univ : Finset κ).Nonempty := ⟨i,Finset.mem_univ _⟩
  obtain ⟨j,_hj,maximum⟩ := Finset.exists_max_image Finset.univ (fun k : κ => ‖v k‖) h₀
  have hpos : 0 < ‖v j‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr (promote_nonzero r.val)) (maximum i (Finset.mem_univ _))
  let u : Overlap (k:=j) a P33 σ embedding (C i) := ⟨r,norm_pos_iff.mp hpos⟩
  let s := transition a P33 σ embedding (C i) (C j) u
  have ssmall : s ∈ dominant a P33 σ embedding C j := by
    change s.val ∈ Metric.closedBall (0 : {k : κ // k≠j} → ℂ) 1
    rw [show s.val=ratio v j from transition_coordinates a P33 σ embedding (C i) (C j) u,
      Metric.mem_closedBall,dist_pi_le_iff zero_le_one]
    intro k
    change dist (v k.val * (v j)⁻¹) 0 ≤ 1
    rw [dist_zero_right,norm_mul,norm_inv,← div_eq_mul_inv,div_le_iff₀ hpos,one_mul]
    exact maximum k.val (Finset.mem_univ _)
  rw [Set.mem_iUnion]
  exact ⟨j,s,ssmall,(same_point a P33 σ embedding (C i) (C j) u).trans hr⟩

theorem actual_compact : CompactSpace P := by
  constructor
  rw [← dominant_cover a P33 σ embedding C]
  exact isCompact_iUnion (fun i =>
    (dominant_compact a P33 σ embedding C i).image (addr_continuous a P33 σ embedding C i))

end OriginalRetainedEuclideanAtlas318
