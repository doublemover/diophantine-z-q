module

public import SelectedActualAbelRegularMeasuredSheetFromInvariant318
import all SelectedActualAbelGenuineLocalMeasuredSheet318
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Measure.WithDensity

public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Topology UpperHalfPlane
open scoped ENNReal
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedWeightTwoPetersson318 SelectedOriginalAbelMeasuredCover318
open SelectedActualAbelOrdinaryChartDensity318 SelectedActualAbelTargetLatticeHaar318
open SelectedActualAbelOrderedPrimitiveSheetCharts318
open SelectedActualAbelGenuineLocalMeasuredSheet318
open SelectedActualAbelRegularMeasuredSheetFromInvariant318
open SelectedActualAbelIdentityChartLifts318 SelectedActualAbelPeriodFromIdentityDifferential318

namespace SelectedActualAbelSourceNullFromInvariant318

variable {M g : ℕ}

def HasRegularPeriod (f : Fin g → Form M) (z : Domain M g) : Prop :=
  ∃ t : Fin g → UpperHalfPlane,
    periodProjection M g t = z ∧ (periodMatrix f t).det ≠ 0

theorem zero_density_of_no_regular_period (f : Fin g → Form M)
    (z : Domain M g) (hz : ¬ HasRegularPeriod f z) : positiveDensity f z = 0 := by
  classical
  have he (j : Fin g) : ∃ t : UpperHalfPlane, quotientMap M t = z j :=
    GammaOneAtlas318.quotient_surjective M (z j)
  choose t ht using he
  have htz : periodProjection M g t = z := by
    unfold periodProjection
    exact funext ht
  have hzero : (periodMatrix f t).det = 0 := by
    by_contra hn
    exact hz ⟨t,htz,hn⟩
  have hd := original_positiveDensity_period f t
  change (positiveDensity f (periodProjection M g t) : ℝ) =
    Complex.normSq (periodMatrix f t).det * ∏ j : Fin g, (t j).im ^ 2 at hd
  rw [htz,hzero,Complex.normSq_zero,zero_mul] at hd
  apply NNReal.coe_injective
  simpa only [NNReal.coe_zero] using hd

variable {J ι : Type*} [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]
  [MeasurableSpace J] [BorelSpace J] [Finite ι]

/-- The ordinary weighted source pulls back every null target set to null.
No premise that the ordinary critical locus is Lebesgue-null is needed:
it has zero determinant density. Regular preimages use the exact actual
local pushforward and second-countable cover. -/
theorem preimage_target_null (hM : 5 ≤ M) (f : Fin g → Form M)
    (L : Submodule ℤ (V g)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (q : V g →+ J) (hq : Continuous q) (hqS : Function.Surjective q)
    (hker : ∀ v : V g, q v = 0 ↔ v ∈ L) (chart : IdentityChart q)
    (a : Base (image M) → J) (ha : Continuous a)
    (hread : InvariantDifferentialEquation f chart a)
    (B : Set J) (hB : MeasurableSet B)
    (hBnull : targetVolume L b (volume : Measure (V g)) q B = 0) :
    pullbackVolume f hM (actualOrderedAbel a ⁻¹' B) = 0 := by
  classical
  let p : UpperHalfPlane → Base (image M) := quotientMap M
  have hp := GammaOneAtlas318.quotient_localHomeomorph M hM
  letI : OpensMeasurableSpace (Base (image M)) :=
    opensMeasurableSpace_iff_forall_measurableSet.mpr
      (fun _ hs => measurableSet_quotient.mpr (hs.preimage hp.continuous).measurableSet)
  letI : SecondCountableTopology (Base (image M)) :=
    (show IsOpenQuotientMap p from
      ⟨GammaOneAtlas318.quotient_surjective M,hp.continuous,hp.isOpenMap⟩).secondCountableTopology
  let ν := targetVolume L b (volume : Measure (V g)) q
  let μ := pullbackVolume f hM
  let A : Domain M g → J := actualOrderedAbel a
  have hA : Continuous A := continuous_finsetSum Finset.univ (fun j _ => ha.comp (continuous_apply j))
  have hAmeas : Measurable A := hA.measurable
  let R : Set (Domain M g) := {z | HasRegularPeriod f z}
  have hpatch (z : R) :
      ∃ D : Set (Domain M g), z.val ∈ D ∧ IsOpen D ∧ μ (A ⁻¹' B ∩ D) = 0 := by
    have hz : HasRegularPeriod f z.val := z.property
    unfold HasRegularPeriod at hz
    obtain ⟨t,ht,hd⟩ := hz
    obtain ⟨D,U,hD,_,htD,_,_,hmap,_⟩ :=
      regular_local_weighted_pushforward hM f L b q hq hqS hker chart a ha hread t hd
    refine ⟨D,ht ▸ htD,hD,?_⟩
    have h := congrArg (fun m : Measure J => m B) hmap
    change Measure.map A (μ.restrict D) B = ν.restrict (q '' U) B at h
    rw [Measure.map_apply hAmeas hB,Measure.restrict_apply (hAmeas hB)] at h
    have hle : ν.restrict (q '' U) B ≤ ν B := Measure.restrict_apply_le _ _
    exact h.trans (le_antisymm (hle.trans_eq hBnull) (by simp))
  choose D hDmem hDopen hDzero using hpatch
  have hcover : R ⊆ ⋃ z : R, D z := fun z hz => Set.mem_iUnion.mpr ⟨⟨z,hz⟩,hDmem ⟨z,hz⟩⟩
  obtain ⟨I,hI,hcov⟩ :=
    (HereditarilyLindelofSpace.isLindelof R).elim_countable_subcover D hDopen hcover
  letI : Countable I := hI.to_subtype
  let N : Set (Domain M g) := ⋃ α : I, A ⁻¹' B ∩ D α.val
  have hN : μ N = 0 := measure_iUnion_null (fun α : I => hDzero α.val)
  let Z : Set (Domain M g) := {x | positiveDensity f x = 0}
  have hZm : MeasurableSet Z := (positiveDensity_measurable f) (measurableSet_singleton 0)
  have hZ : μ Z = 0 := by
    change ((productArea (g := g) hM).withDensity fun x =>
      ((positiveDensity f x : NNReal) : ℝ≥0∞)) Z = 0
    rw [withDensity_apply _ hZm]
    apply setLIntegral_eq_zero hZm
    intro x hx
    have he : positiveDensity f x = 0 := hx
    change ((positiveDensity f x : NNReal) : ℝ≥0∞) = 0
    rw [he,ENNReal.coe_zero] <;> rfl
  have hsub : A ⁻¹' B ⊆ Z ∪ N := by
    intro z hz
    by_cases hr : z ∈ R
    · obtain ⟨α,hα⟩ := Set.mem_iUnion.mp (hcov hr)
      obtain ⟨hαI,hαD⟩ := Set.mem_iUnion.mp hα
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨α,hαI⟩,hz,hαD⟩)
    · exact Or.inl (zero_density_of_no_regular_period f z hr)
  exact measure_mono_null hsub (measure_union_null hZ hN)

end SelectedActualAbelSourceNullFromInvariant318

#print axioms SelectedActualAbelSourceNullFromInvariant318.zero_density_of_no_regular_period
#print axioms SelectedActualAbelSourceNullFromInvariant318.preimage_target_null
