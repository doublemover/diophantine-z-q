module

public import SelectedActualAbelSameExponentialLatticeQuotient318
public import SelectedActualAbelTargetLatticeHaar318
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

public section
noncomputable section

open Set MeasureTheory MeasureTheory.Measure Topology
open SelectedActualAbelIdentityChartLifts318 SelectedActualAbelSameExponentialLatticeQuotient318
open SelectedActualAbelTargetLatticeHaar318

namespace SelectedActualAbelExponentialNullTransfer318

section LocalChart

variable {E T ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [AddCommGroup T] [MeasurableSpace T] [Finite ι]

/-- Exact comparison on arbitrary subsets of the actual logarithm chart.
The discarded or critical coordinate image need not be Borel. The proof
uses the same unnormalized lattice-box measure as the measured sheets,
and not another reference measure on the Jacobian. -/
theorem actual_log_chart_measure
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (μ : Measure E) [IsAddHaarMeasure μ]
    (q : E →+ T) (hq : Measurable q)
    (hker : ∀ v : E, q v = 0 ↔ v ∈ L)
    (U A : Set E) (hU : MeasurableSet U) (hA : A ⊆ U)
    (hchart : MeasurableEmbedding (fun x : U => q x)) :
    targetVolume L b μ q (q '' A) = μ A := by
  let e : U → T := fun x => q x
  let v : U → E := Subtype.val
  let m : Measure U := μ.comap v
  have he : MeasurableEmbedding e := hchart
  have hv : MeasurableEmbedding v := MeasurableEmbedding.subtype_coe hU
  have hqU : Set.range e = q '' U := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨(x : E),x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  have hW : MeasurableSet (q '' U) := hqU ▸ he.measurableSet_range
  have hi : InjOn q U := by
    intro x hx y hy h
    exact congrArg v (he.injective (show e ⟨x,hx⟩ = e ⟨y,hy⟩ from h))
  have hm : m.map v = μ.restrict U := _root_.map_comap_subtype_coe hU μ
  have hmap : (μ.restrict U).map q = m.map e := by
    rw [← hm, Measure.map_map hq hv.measurable] <;> rfl
  have hpre : e ⁻¹' (q '' A) = v ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨a,ha,hax⟩
      have hax' : a = (x : E) := hi (hA ha) x.property hax
      change (x : E) ∈ A
      exact Eq.mp (congrArg (fun z : E => z ∈ A) hax') ha
    · intro hx
      exact ⟨v x,hx,rfl⟩
  calc
    targetVolume L b μ q (q '' A) =
        (targetVolume L b μ q).restrict (q '' U) (q '' A) :=
      by rw [Measure.restrict_apply' hW, Set.inter_eq_left.mpr (Set.image_mono hA)]
    _ = ((μ.restrict U).map q) (q '' A) :=
      congrArg (fun m' : Measure T => m' (q '' A))
        (targetVolume_restrict_chart L b μ q hq hker U hU hi hW)
    _ = (m.map e) (q '' A) := congrArg (fun m' : Measure T => m' (q '' A)) hmap
    _ = m (v ⁻¹' A) := (he.map_apply m _).trans (congrArg (fun s : Set U => m s) hpre)
    _ = (m.map v) A := (hv.map_apply m A).symm
    _ = μ A := by rw [hm, Measure.restrict_apply' hU, Set.inter_eq_left.mpr hA]
end LocalChart

variable {g : ℕ} {J ι : Type*}
variable [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]
  [MeasurableSpace J] [BorelSpace J] [Finite ι]

/-- Proof through the actual exponential charts, for arbitrary subsets,
not only Borel ones. Good as an outer-volume comparison for Sard and
discarded images even when the intermediates are not Borel. -/
theorem image_null_through_actual_exponential
    (L : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (q : (Fin g → ℂ) →+ J) (hq : Continuous q)
    (hker : ∀ v : (Fin g → ℂ), q v = 0 ↔ v ∈ L) (chart : IdentityChart q)
    (N : Set (Fin g → ℂ)) (hN : (volume : Measure (Fin g → ℂ)) N = 0) :
    targetVolume L b (volume : Measure (Fin g → ℂ)) q (q '' N) = 0 := by
  classical
  obtain ⟨U,hU,h0,hInj⟩ := exists_open_local_injectivity q chart
  let W (x : (Fin g → ℂ)) : Set (Fin g → ℂ) := (fun z : (Fin g → ℂ) => z - x) ⁻¹' U
  have hW (x : (Fin g → ℂ)) : IsOpen (W x) := hU.preimage (continuous_id.fun_sub continuous_const)
  have hxW (x : (Fin g → ℂ)) : x ∈ W x := by
    change x - x ∈ U
    rw [sub_self]
    exact h0
  have hWI (x : (Fin g → ℂ)) : InjOn q (W x) := by
    intro v hv w hw e
    have hvw : q (v - x) = q (w - x) := by rw [map_sub,map_sub,e]
    have he : v - x = w - x := hInj hv hw hvw
    exact (sub_add_cancel v x).symm.trans
      ((congrArg (fun a : Fin g → ℂ => a + x) he).trans (sub_add_cancel w x))
  have hOpen := actual_exponential_isOpenMap q hq chart
  have hEmb (x : (Fin g → ℂ)) : MeasurableEmbedding (fun z : W x => q z) := by
    have hop : IsOpenMap (fun z : W x => q z) := hOpen.comp (hW x).isOpenMap_subtype_val
    have hc : Continuous (fun z : W x => q z) := hq.comp continuous_subtype_val
    have hi : Function.Injective (fun z : W x => q z) :=
      fun z z' he => Subtype.ext (hWI x z.property z'.property he)
    exact (IsOpenEmbedding.of_continuous_injective_isOpenMap hc hi hop).measurableEmbedding
  let ν := targetVolume L b (volume : Measure (Fin g → ℂ)) q
  have hLocal (x : (Fin g → ℂ)) : ν (q '' (N ∩ W x)) = 0 := by
    calc
      ν (q '' (N ∩ W x)) = (volume : Measure (Fin g → ℂ)) (N ∩ W x) :=
        actual_log_chart_measure L b volume q hq.measurable hker
          (W x) (N ∩ W x) (hW x).measurableSet inter_subset_right (hEmb x)
      _ = 0 := measure_mono_null inter_subset_left hN
  have hcover : N ⊆ ⋃ x : (Fin g → ℂ), W x := fun x _ => Set.mem_iUnion.mpr ⟨x,hxW x⟩
  obtain ⟨I,hI,hCov⟩ :=
    (HereditarilyLindelofSpace.isLindelof N).elim_countable_subcover W hW hcover
  letI : Countable I := hI.to_subtype
  have hs : q '' N ⊆ ⋃ i : I, q '' (N ∩ W i.val) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hCov hx)
    obtain ⟨hiI,hix⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨⟨i,hiI⟩,x,⟨hx,hix⟩,rfl⟩
  exact measure_mono_null hs (measure_iUnion_null fun i : I => hLocal i.val)

end SelectedActualAbelExponentialNullTransfer318

#print axioms SelectedActualAbelExponentialNullTransfer318.actual_log_chart_measure
#print axioms SelectedActualAbelExponentialNullTransfer318.image_null_through_actual_exponential
