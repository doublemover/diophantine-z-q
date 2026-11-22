module

public import SelectedActualAbelRegularMeasuredSheetFromInvariant318
public import SelectedActualAbelLocalToCountedMeasure318
public import SelectedActualAbelSourceNullFromInvariant318
import all SelectedActualAbelLocalToCountedMeasure318
import Mathlib.Topology.IsLocalHomeomorph

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Set Topology UpperHalfPlane
open scoped BigOperators ENNReal Matrix Topology
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedWeightTwoPetersson318 SelectedConstructPeterssonFrame318
open SelectedOriginalAbelMeasuredCover318 SelectedOriginalAbelSumGramIntegral318
open SelectedAbelFiniteSheetMeasure318 SelectedActualAbelLocalToCountedMeasure318
open SelectedActualAbelPointwiseDerivative318 SelectedActualAbelTargetLatticeHaar318
open SelectedActualAbelOrdinaryChartDensity318 SelectedActualAbelOrderedPrimitiveSheetCharts318
open SelectedActualAbelGenuineLocalMeasuredSheet318 SelectedActualAbelRegularMeasuredSheetFromInvariant318
open SelectedActualAbelIdentityChartLifts318 SelectedActualAbelPeriodFromIdentityDifferential318
open SelectedActualAbelSourceNullFromInvariant318

namespace SelectedActualAbelCompactVolumeFromInvariant318

variable {M g : ℕ} {X J ι : Type*}
variable [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]
  [T2Space J] [SecondCountableTopology J] [MeasurableSpace J] [BorelSpace J] [Finite ι]

private theorem quotient_product_opens (hM : 5 ≤ M) :
    OpensMeasurableSpace (Domain M g) := by
  let p : UpperHalfPlane → Base (image M) := quotientMap M
  have hp := GammaOneAtlas318.quotient_localHomeomorph M hM
  letI : OpensMeasurableSpace (Base (image M)) :=
    opensMeasurableSpace_iff_forall_measurableSet.mpr
      (fun _ hs => measurableSet_quotient.mpr (hs.preimage hp.continuous).measurableSet)
  letI : SecondCountableTopology (Base (image M)) :=
    (show IsOpenQuotientMap p from
      ⟨GammaOneAtlas318.quotient_surjective M,hp.continuous,hp.isOpenMap⟩).secondCountableTopology
  unfold Domain
  infer_instance

/-- The same *actual* ordinary quotient embeds into the given compact
ordered source. Its Abel map A restricts to the sum of degree-one values.
The supplied geometric good locus excludes precisely the points not
witnessed regular in the literal ordered period coordinates. Analytic
local sheets, measured local laws, and their global counted pushforward
are produced, not supplied. -/
theorem compact_counted_abel_measure (hM : 5 ≤ M) (f : Fin g → Form M)
    (L : Submodule ℤ (V g)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (q : V g →+ J) (hq : Continuous q) (hqS : Surjective q)
    (hker : ∀ v : V g, q v = 0 ↔ v ∈ L)
    (chart : IdentityChart q) (a : Base (image M) → J) (ha : Continuous a)
    (hread : InvariantDifferentialEquation f chart a)
    (i : Domain M g → X) (hi : IsOpenEmbedding i) (A : X → J) (hA : Continuous A)
    (hAi : ∀ z, A (i z) = actualOrderedAbel a z)
    (G : Set J) (hG : IsOpen G)
    (hgood : ∀ x ∈ A ⁻¹' G, ∃ t : Fin g → UpperHalfPlane,
      x = i (periodProjection M g t) ∧ (periodMatrix f t).det ≠ 0)
    (hdegree : ∀ y ∈ G, Nonempty ((A ⁻¹' {y}) ≃ Fin g.factorial))
    (hTnull : targetVolume L b (volume : Measure (V g)) q Gᶜ = 0) :
    Measure.map A (Measure.map i (pullbackVolume f hM)) =
      (g.factorial : ℝ≥0∞) • targetVolume L b (volume : Measure (V g)) q := by
  classical
  letI := quotient_product_opens (g := g) hM
  let μ : Measure X := (pullbackVolume f hM).map i
  let ν : Measure J := targetVolume L b (volume : Measure (V g)) q
  have hiM : Measurable i := hi.continuous.measurable
  have hAi' : A ∘ i = actualOrderedAbel a := funext hAi
  have hchart : ∀ x ∈ A ⁻¹' G, ∃ D : Set X, IsOpen D ∧ x ∈ D ∧ InjOn A D ∧
      Measure.map A (μ.restrict D) = ν.restrict (A '' D) ∧
      IsOpenMap (D.domRestrict A) := by
    intro x hx
    obtain ⟨t,rfl,ht⟩ := hgood x hx
    obtain ⟨O,U,hO,_,hz,hOinj,hOU,hMeasure,hOopen⟩ :=
      regular_local_weighted_pushforward hM f L b q hq hqS hker chart a ha hread t ht
    let D := i '' O
    have hD : IsOpen D := hi.isOpenMap _ hO
    have hZD : i (periodProjection M g t) ∈ D := ⟨periodProjection M g t,hz,rfl⟩
    have hDinj : InjOn A D := by
      rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ he
      apply congrArg i
      exact hOinj hv hw ((hAi v).symm.trans (he.trans (hAi w)))
    have hDimage : A '' D = actualOrderedAbel a '' O := by
      ext y
      constructor
      · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
        exact ⟨z,hz,(hAi z).symm⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨i z,⟨z,hz,rfl⟩,hAi z⟩
    have hDpre : i ⁻¹' D = O := by
      ext z
      constructor
      · rintro ⟨w,hw,he⟩
        exact hi.injective he ▸ hw
      · intro hz
        exact ⟨z,hz,rfl⟩
    have hDm : Measure.map A (μ.restrict D) = ν.restrict (A '' D) := by
      change Measure.map A (((pullbackVolume f hM).map i).restrict D) = _
      rw [Measure.restrict_map hiM hD.measurableSet,hDpre,
        Measure.map_map hA.measurable hiM,hAi',hDimage,hOU]
      exact hMeasure
    refine ⟨D,hD,hZD,hDinj,hDm,?_⟩
    intro W hW
    let T : Set X := Subtype.val '' W
    have hT : IsOpen T := hD.isOpenMap_subtype_val _ hW
    have hTD : T ⊆ D := by
      rintro _ ⟨z,_,rfl⟩
      exact z.property
    let S : Set (Domain M g) := i ⁻¹' T
    have hS : IsOpen S := hT.preimage hi.continuous
    have hSO : S ⊆ O := by
      intro z hz
      have he := hTD hz
      change z ∈ i ⁻¹' D at he
      rw [hDpre] at he
      exact he
    have hSW : (D.domRestrict A) '' W = actualOrderedAbel a '' S := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        obtain ⟨v,_,hv⟩ := z.property
        exact ⟨v,⟨z,hz,hv.symm⟩,(hAi v).symm.trans (congrArg A hv)⟩
      · rintro ⟨v,hv,rfl⟩
        obtain ⟨z,hz,he⟩ := hv
        exact ⟨z,hz,(congrArg A he).trans (hAi v)⟩
    rw [hSW]
    exact hOopen S hS hSO
  have hLocal : LocalMeasureLaw A G μ ν := by
    unfold LocalMeasureLaw
    intro x hx
    obtain ⟨D,hD,hxD,hiD,hmD,_⟩ := hchart x hx
    exact ⟨D,hD,hxD,hiD,hmD⟩
  have hTopo : IsLocalHomeomorphOn A (A ⁻¹' G) := by
    apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict (A ⁻¹' G) (f := A)).mpr
    intro x hx
    obtain ⟨D,hD,hxD,hiD,_,hoD⟩ := hchart x hx
    refine ⟨D,hD.mem_nhds hxD,IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ hoD⟩
    · change Continuous (fun z : D => A z)
      exact hA.comp continuous_subtype_val
    · intro v w he
      exact Subtype.ext (hiD v.property w.property he)
  have hSnull : μ (A ⁻¹' Gᶜ) = 0 := by
    have hMeas : MeasurableSet (A ⁻¹' Gᶜ) := hA.measurable hG.measurableSet.compl
    have hSet : i ⁻¹' (A ⁻¹' Gᶜ) = actualOrderedAbel a ⁻¹' Gᶜ := by
      ext z
      change (A (i z) ∈ Gᶜ) ↔ (actualOrderedAbel a z ∈ Gᶜ)
      rw [hAi]
    change Measure.map i (pullbackVolume f hM) (A ⁻¹' Gᶜ) = 0
    rw [Measure.map_apply hiM hMeas,hSet]
    exact preimage_target_null hM f L b q hq hqS hker chart a ha hread
      Gᶜ hG.measurableSet.compl hTnull
  exact map_eq_count_of_local_laws μ ν g.factorial A hA hA.measurable G hG
    hTopo hdegree hLocal hSnull hTnull

/-- The actual original Gram volume, from the single canonical lattice and
the true compact Abel map. No global change-of-variables or supplied
measure atlas. The inputs still include the actual compact algebraic/analytic
identification, genuine RR/Sard good data, and the same invariant readout. -/
theorem compact_abel_haar_volume_eq_gram (hM : 5 ≤ M) (f : Fin g → Form M)
    (L : Submodule ℤ (V g)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (q : V g →+ J) (hq : Continuous q) (hqS : Surjective q)
    (hker : ∀ v : V g, q v = 0 ↔ v ∈ L)
    (chart : IdentityChart q) (a : Base (image M) → J) (ha : Continuous a)
    (hread : InvariantDifferentialEquation f chart a)
    (i : Domain M g → X) (hi : IsOpenEmbedding i) (A : X → J) (hA : Continuous A)
    (hAi : ∀ z, A (i z) = actualOrderedAbel a z)
    (G : Set J) (hG : IsOpen G)
    (hgood : ∀ x ∈ A ⁻¹' G, ∃ t : Fin g → UpperHalfPlane,
      x = i (periodProjection M g t) ∧ (periodMatrix f t).det ≠ 0)
    (hdegree : ∀ y ∈ G, Nonempty ((A ⁻¹' {y}) ≃ Fin g.factorial))
    (hTnull : targetVolume L b (volume : Measure (V g)) q Gᶜ = 0) :
    (((targetVolume L b (volume : Measure (V g)) q) Set.univ).toReal : ℂ) =
      (originalGram hM f).det := by
  letI := quotient_product_opens (g := g) hM
  let ν := targetVolume L b (volume : Measure (V g)) q
  have hiM : Measurable i := hi.continuous.measurable
  have hm := compact_counted_abel_measure hM f L b q hq hqS hker chart a ha hread
    i hi A hA hAi G hG hgood hdegree hTnull
  rw [Measure.map_map hA.measurable hiM] at hm
  have hD : complexDensity f =ᵐ[productArea (g := g) hM]
      fun x => (((positiveDensity f x : ℝ)) : ℂ) :=
    Filter.Eventually.of_forall (image_of_positiveDensity f)
  have hc := complex_integral_eq_count_of_density (hA.measurable.comp hiM)
    ν (productArea (g := g) hM) (positiveDensity f) (positiveDensity_measurable f)
    (complexDensity f) hD hm
  exact volume_eq_gram hM f _ hc.symm

end SelectedActualAbelCompactVolumeFromInvariant318

#print axioms SelectedActualAbelCompactVolumeFromInvariant318.compact_counted_abel_measure
#print axioms SelectedActualAbelCompactVolumeFromInvariant318.compact_abel_haar_volume_eq_gram
