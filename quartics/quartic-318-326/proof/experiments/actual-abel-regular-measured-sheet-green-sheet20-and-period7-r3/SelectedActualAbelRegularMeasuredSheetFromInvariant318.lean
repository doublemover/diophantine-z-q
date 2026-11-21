module

public import SelectedActualAbelGenuineLocalMeasuredSheet318
public import SelectedActualAbelOrderedPrimitiveSheetCharts318
public import SelectedActualAbelSameExponentialLatticeQuotient318
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

public section

noncomputable section

open Filter Function Matrix MeasureTheory MeasureTheory.Measure Set Topology UpperHalfPlane
open scoped BigOperators ENNReal Topology
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedWeightTwoPetersson318 SelectedOriginalAbelMeasuredCover318
open SelectedActualAbelOrdinaryChartDensity318 SelectedActualAbelTargetLatticeHaar318
open SelectedActualAbelFlatPeriodProductCoordinates318 SelectedActualAbelPointwiseDerivative318
open SelectedActualOrdinaryAbelPeriodMap318 SelectedActualAbelIdentityChartLifts318
open SelectedActualAbelPeriodFromIdentityDifferential318 SelectedActualAbelPeriodAgreement318
open SelectedActualAbelOrderedPrimitiveSheetCharts318
open SelectedActualAbelGenuineLocalMeasuredSheet318
open SelectedActualAbelSameExponentialLatticeQuotient318

namespace SelectedActualAbelRegularMeasuredSheetFromInvariant318

variable {M g : ℕ}

/-- Extend the literal ordered matrix outside the open period product for use
in total Borel pushforwards. It has its exact native entry at every true period. -/
def matrixExtension (f : Fin g → Form M) :
    V g → Matrix (Fin g) (Fin g) ℂ := by
  classical
  exact (fullPeriods g).piecewise (rowMatrix f) (fun _ => 0)

theorem matrixExtension_true (f : Fin g → Form M) (x : V g) (hx : x ∈ fullPeriods g) :
    matrixExtension f x = rowMatrix f x := by
  unfold matrixExtension
  exact Set.piecewise_eq_of_mem _ _ _ hx

private theorem matrixExtension_weight (f : Fin g → Form M) :
    Measurable (fun x => ENNReal.ofReal (Complex.normSq (matrixExtension f x).det)) := by
  classical
  have hR : Continuous (fun x : fullPeriods g => rowMatrix f (x : V g)) := by
    apply continuous_matrix
    intro i j
    apply continuous_iff_continuousAt.mpr
    intro x
    have hz : (x : V g) j ∈ upperHalfPlaneSet := x.property j (Set.mem_univ j)
    have ht : ContinuousAt (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane) ((x : V g) j) :=
      (UpperHalfPlane.mdifferentiableAt_ofComplex hz).continuousAt
    have hj : Continuous (fun z : fullPeriods g => (z : V g) j) :=
      (continuous_apply j).comp continuous_subtype_val
    have hf : Continuous (fun t : UpperHalfPlane => f i t) := ModularFormClass.continuous (f i)
    have hComp : ContinuousAt (fun z : fullPeriods g => UpperHalfPlane.ofComplex ((z : V g) j)) x :=
      ContinuousAt.comp' (f := fun z : fullPeriods g => (z : V g) j) ht hj.continuousAt
    change ContinuousAt (fun z : fullPeriods g => f i (UpperHalfPlane.ofComplex ((z : V g) j))) x
    exact ContinuousAt.comp' (f := fun z : fullPeriods g => UpperHalfPlane.ofComplex ((z : V g) j))
      hf.continuousAt hComp
  have hC : ContinuousOn (rowMatrix f) (fullPeriods g) :=
    continuousOn_iff_continuous_domRestrict.2 hR
  have hm : Measurable (matrixExtension f) := by
    unfold matrixExtension
    exact hC.measurable_piecewise continuousOn_const (fullPeriods_open g).measurableSet
  have hdet : Continuous (fun A : Matrix (Fin g) (Fin g) ℂ => A.det) := continuous_id.matrix_det
  exact ENNReal.continuous_ofReal.measurable.comp
    (Complex.continuous_normSq.measurable.comp (hdet.measurable.comp hm))

private theorem actual_rectangle {M g : ℕ} (hM : 5 ≤ M) (t : Fin g → UpperHalfPlane) :
    ∃ B : Fin g → Set UpperHalfPlane, (∀ j, IsOpen (B j)) ∧
      (∀ j, t j ∈ B j) ∧ (∀ j, InjOn (quotientMap M) (B j)) := by
  have h j : ∃ B : Set UpperHalfPlane, IsOpen B ∧
      t j ∈ B ∧ InjOn (quotientMap M) B := by
    obtain ⟨e,he,hq⟩ := GammaOneAtlas318.quotient_localHomeomorph M hM (t j)
    exact ⟨e.source,e.open_source,he,hq.symm ▸ e.injOn⟩
  choose B hB ht hi using h
  exact ⟨B,hB,ht,hi⟩

private theorem flatRectangle_open (B : Fin g → Set UpperHalfPlane) (hB : ∀ j, IsOpen (B j)) :
    IsOpen (flatRectangle B) :=
  isOpen_set_pi Set.finite_univ (fun j _ => UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ (hB j))

private theorem flatRectangle_subset (B : Fin g → Set UpperHalfPlane) :
    flatRectangle B ⊆ fullPeriods g := by
  intro x hx j hj
  obtain ⟨t,_,h⟩ := hx j hj
  rw [← h]
  exact t.im_pos

variable {J ι : Type*} [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]
  [MeasurableSpace J] [BorelSpace J] [Finite ι]

private theorem exponential_target_neighborhood (q : V g →+ J) (chart : IdentityChart q) (x : V g) :
    ∃ W : Set (V g), IsOpen W ∧ x ∈ W ∧ InjOn q W := by
  obtain ⟨U,hU,hzero,hqi⟩ := exists_open_local_injectivity q chart
  let T (v : V g) : V g := v - x
  have hT : Continuous T := continuous_id.fun_sub continuous_const
  refine ⟨T ⁻¹' U,hU.preimage hT,?_,?_⟩
  · change x - x ∈ U
    rw [sub_self]
    exact hzero
  · intro v hv w hw he
    have h : q (T v) = q (T w) := by
      change q (v - x) = q (w - x)
      rw [map_sub,map_sub,he]
    exact sub_right_injective (hqi hv hw h)

abbrev actualOrderedAbel (a : Base (image M) → J) (z : Domain M g) : J :=
  ∑ j : Fin g, a (z j)

/-- At each ordinary tuple with nonzero original period determinant, the
analytic invariant differential constructs an actual open sheet and its
exact local weighted pushforward into the same Haar measure. No chart,
measurable image, local inverse, germ, or matching readout is assumed. -/
theorem regular_local_weighted_pushforward (hM : 5 ≤ M) (f : Fin g → Form M)
    (L : Submodule ℤ (V g)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (q : V g →+ J) (hq : Continuous q) (hqS : Surjective q)
    (hker : ∀ v : V g, q v = 0 ↔ v ∈ L)
    (chart : IdentityChart q) (a : Base (image M) → J) (ha : Continuous a)
    (hread : InvariantDifferentialEquation f chart a) (t : Fin g → UpperHalfPlane)
    (hdet : (periodMatrix f t).det ≠ 0) :
    ∃ D : Set (Domain M g), ∃ U : Set (V g), IsOpen D ∧ IsOpen U ∧
      periodProjection M g t ∈ D ∧ InjOn (actualOrderedAbel a) D ∧
      actualOrderedAbel a '' D = q '' U ∧
      Measure.map (actualOrderedAbel a) ((pullbackVolume f hM).restrict D) =
        (targetVolume L b (volume : Measure (V g)) q).restrict (q '' U) ∧
      ∀ O : Set (Domain M g), IsOpen O → O ⊆ D → IsOpen (actualOrderedAbel a '' O) := by
  classical
  let p₁ : UpperHalfPlane → Base (image M) := quotientMap M
  have hq₁ := GammaOneAtlas318.quotient_localHomeomorph M hM
  letI : OpensMeasurableSpace (Base (image M)) :=
    opensMeasurableSpace_iff_forall_measurableSet.mpr fun s hs =>
      measurableSet_quotient.mpr (hs.preimage hq₁.continuous).measurableSet
  letI : SecondCountableTopology (Base (image M)) :=
    (show IsOpenQuotientMap p₁ from
      ⟨GammaOneAtlas318.quotient_surjective M,hq₁.continuous,hq₁.isOpenMap⟩).secondCountableTopology
  have hp : IsOpenMap (periodProjection M g) :=
    IsOpenMap.piMap (f := fun _ : Fin g => p₁) (fun _ => hq₁.isOpenMap)
      (Filter.Eventually.of_forall (fun _ => GammaOneAtlas318.quotient_surjective M))
  have hpa : Continuous (actualOrderedAbel (g := g) a) :=
    continuous_finsetSum Finset.univ (fun j _ => ha.comp (continuous_apply j))
  have hpc : Continuous (periodCoords (ι := Fin g)) :=
    continuous_pi fun j => UpperHalfPlane.continuous_coe.comp (continuous_apply j)
  obtain ⟨c,hF,hRead,_⟩ := exists_ordered_lift_from_invariant_differential
    hM f q hq hqS chart a ha hread
  obtain ⟨B,hB,htB,hBi⟩ := actual_rectangle hM t
  let x := periodCoords t
  have hx : x ∈ flatRectangle B := fun j _ => ⟨t j,htB j,rfl⟩
  have ht : t ∈ upstairsRectangle B := fun j _ => htB j
  have hmatrix : rowMatrix f x = periodMatrix f t := by
    unfold x periodCoords periodMatrix
    exact rowMatrix_coe f t
  have hxdet : (rowMatrix f x).det ≠ 0 := by rw [hmatrix]; exact hdet
  obtain ⟨W,hW,hFW,hWq⟩ := exponential_target_neighborhood q chart (liftSum f c x)
  obtain ⟨S,U,hS,hU,hxS,hSB,hUW,hFi,hFU,hFo⟩ := exists_regular_ordered_sheet f c x
    (flatRectangle B) W (flatRectangle_open B hB) hW hx (flatRectangle_subset B) hFW hxdet
  let T : Set (upstairs g) := periodCoords ⁻¹' S ∩ upstairsRectangle B
  let D : Set (Domain M g) := ordinarySheet M g B S
  have hT : IsOpen T :=
    (hS.preimage hpc).inter (isOpen_set_pi Set.finite_univ (fun j _ => hB j))
  have hD : IsOpen D := hp T hT
  have hUq : InjOn q U := hWq.mono hUW
  have hqU : IsOpen (q '' U) := actual_exponential_isOpenMap q hq chart _ hU
  have hreg : ∀ u ∈ T, actualOrderedAbel a (periodProjection M g u) =
      q (liftSum f c (periodCoords u)) := by
    intro u _
    unfold periodCoords periodProjection actualOrderedAbel
    exact (hRead u).symm
  have hCread : ∀ u ∈ upstairsRectangle B,
      matrixExtension f (periodCoords u) = periodMatrix f u := by
    intro u _
    have hu : periodCoords u ∈ fullPeriods g := fun j _ => (u j).im_pos
    rw [matrixExtension_true f (periodCoords u) hu]
    unfold periodCoords periodMatrix
    exact rowMatrix_coe f u
  have hgerm : ∀ y ∈ S, ∃ (φ : Fin g → Fin g → ℂ → ℂ) (z : V g),
      (∀ i j, HasDerivAt (φ i j) (matrixExtension f y i j) (y j)) ∧
      liftSum f c =ᶠ[𝓝 y] fun u i => z i + ∑ j, φ i j (u j) := by
    intro y hy
    have hy' := flatRectangle_subset B (hSB hy)
    refine ⟨fun i _ => primitive (f i),translation c,?_,liftSum_germ f c y hy'⟩
    rw [matrixExtension_true f y hy']
    exact liftSum_column f y hy'
  have hm := actual_ordinary_abel_sheet hM f L b q hq.measurable hker
    (actualOrderedAbel a) hpa.measurable (liftSum f c) hF (matrixExtension f)
    (matrixExtension_weight f) B hB hBi S U hS.measurableSet hSB hD.measurableSet
    hU.measurableSet hUq hqU.measurableSet hCread hreg hgerm hFi hFU
  refine ⟨D,U,hD,hU,⟨t,⟨hxS,ht⟩,rfl⟩,?_,?_,hm,?_⟩
  · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ he
    have hUu : liftSum f c (periodCoords u) ∈ U := by
      rw [← hFU]
      exact ⟨periodCoords u,hu.1,rfl⟩
    have hUv : liftSum f c (periodCoords v) ∈ U := by
      rw [← hFU]
      exact ⟨periodCoords v,hv.1,rfl⟩
    have hs := hUq hUu hUv ((hreg u hu).symm.trans (he.trans (hreg v hv)))
    exact congrArg (periodProjection M g)
      (periodCoords_injective (hFi hu.1 hv.1 hs))
  · ext y
    constructor
    · rintro ⟨_,⟨u,hu,rfl⟩,rfl⟩
      refine ⟨liftSum f c (periodCoords u),?_,(hreg u hu).symm⟩
      rw [← hFU]
      exact ⟨periodCoords u,hu.1,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      have hz' : z ∈ liftSum f c '' S := by rw [hFU]; exact hz
      obtain ⟨v,hv,rfl⟩ := hz'
      let u : Fin g → UpperHalfPlane := fun j => UpperHalfPlane.ofComplex (v j)
      have hvB := hSB hv
      have huv : periodCoords u = v := by
        funext j
        obtain ⟨w,_,hw⟩ := hvB j (Set.mem_univ j)
        change (UpperHalfPlane.ofComplex (v j) : ℂ) = v j
        rw [← hw,UpperHalfPlane.ofComplex_apply]
      have huB : u ∈ upstairsRectangle B := by
        intro j hj
        obtain ⟨w,hwB,hw⟩ := hvB j hj
        change UpperHalfPlane.ofComplex (v j) ∈ B j
        rw [← hw,UpperHalfPlane.ofComplex_apply]
        exact hwB
      have hu : u ∈ T := by
        change periodCoords u ∈ S ∧ u ∈ upstairsRectangle B
        rw [huv]
        exact ⟨hv,huB⟩
      have hval := hreg u hu
      rw [huv] at hval
      exact ⟨periodProjection M g u,⟨u,hu,rfl⟩,hval⟩
  · intro O hO hOD
    have hpp : Continuous (periodProjection M g) :=
      continuous_pi fun j => hq₁.continuous.comp (continuous_apply j)
    have hcoordOpen : IsOpenMap (periodCoords (ι := Fin g)) := by
      have he : IsOpenEmbedding (periodCoords (ι := Fin g)) :=
        Topology.IsOpenEmbedding.piMap
          (f := fun _ : Fin g => (UpperHalfPlane.coe : UpperHalfPlane → ℂ))
          (fun _ => UpperHalfPlane.isOpenEmbedding_coe)
      exact he.isOpenMap
    let Z : Set (upstairs g) := periodProjection M g ⁻¹' O ∩ T
    have hZ : IsOpen Z := (hO.preimage hpp).inter hT
    have hzS : periodCoords '' Z ⊆ S := by
      rintro _ ⟨u,hu,rfl⟩
      exact hu.2.1
    have hOeq : actualOrderedAbel a '' O =
        q '' (liftSum f c '' (periodCoords '' Z)) := by
      ext y
      constructor
      · rintro ⟨v,hv,rfl⟩
        obtain ⟨u,hu,rfl⟩ : v ∈ D := hOD hv
        exact ⟨liftSum f c (periodCoords u),
          ⟨periodCoords u,⟨u,⟨hv,hu⟩,rfl⟩,rfl⟩,(hreg u hu).symm⟩
      · rintro ⟨_,⟨_,⟨u,hu,rfl⟩,rfl⟩,rfl⟩
        exact ⟨periodProjection M g u,hu.1,hreg u hu.2⟩
    rw [hOeq]
    exact actual_exponential_isOpenMap q hq chart _ (hFo _ (hcoordOpen _ hZ) hzS)

end SelectedActualAbelRegularMeasuredSheetFromInvariant318

#print axioms SelectedActualAbelRegularMeasuredSheetFromInvariant318.regular_local_weighted_pushforward
