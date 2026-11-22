module

public import AllCuspHausdorff318
public import AllCuspCompact318
public import ActualJFinite318
public import SelectedActualAbelDiscardedTargetNullWithoutCuspJets318
public import SelectedActualAbelOrderedPrimitiveSheetCharts318
public import SelectedActualAbelOrdinaryChartDensity318
public import SelectedActualAbelExceptionalSetNull318
import all SelectedActualAbelOrdinaryChartDensity318
import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section
noncomputable section

open Filter Function MeasureTheory Set Topology UpperHalfPlane
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open AllCuspFilling318 FiniteCuspEnds318 QuotientJ318 DerivativeCocycle318
open SelectedWeightTwoPetersson318 SelectedActualAbelOrderedPrimitiveSheetCharts318
open SelectedActualAbelOrdinaryChartDensity318 SelectedActualAbelPointwiseDerivative318
open SelectedActualAbelExponentialNullTransfer318
open SelectedActualAbelDiscardedTargetNullWithoutCuspJets318
open SelectedActualAbelTargetLatticeHaar318 SelectedActualAbelIdentityChartLifts318
open SelectedActualAbelPeriodFromIdentityDifferential318
open scoped BigOperators Topology

namespace SelectedActualFilledAbelGoodTargetDistinct318

/-- Only the literal cusps and the two actual coarse-j fibres are
discarded. No selected arithmetic fibre is used to build the good set. -/
def discarded (N : ℕ) (hN : 5 ≤ N) : Set (Filled N hN) :=
  Set.range (cusp N hN) ∪
    (original N hN '' ((jMap N) ⁻¹' ({0} : Set ℂ))) ∪
    (original N hN '' ((jMap N) ⁻¹' ({1728} : Set ℂ)))

theorem discarded_finite (N : ℕ) (hN : 5 ≤ N) : (discarded N hN).Finite := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 5) hN)⟩
  have hc : (Set.range (cusp N hN)).Finite := Set.finite_range _
  have h₀ := (ActualJFinite318.finite_fiber N hN 0).image (original N hN)
  have h₁ := (ActualJFinite318.finite_fiber N hN 1728).image (original N hN)
  exact (hc.union h₀).union h₁

variable {g : ℕ}

def orderedDiscarded (N : ℕ) (hN : 5 ≤ N) :
    Set (Fin g → Filled N hN) :=
  ⋃ i, (fun z : Fin g → Filled N hN => z i) ⁻¹' discarded N hN

private theorem outside_discarded_is_period (N : ℕ) (hN : 5 ≤ N)
    (x : Filled N hN) (hx : x ∉ discarded N hN) :
    ∃ t : UpperHalfPlane, original N hN (quotientMap N t) = x := by
  rcases original_or_cusp N hN x with ⟨y,hy⟩ | ⟨c,hc⟩
  · obtain ⟨t,ht⟩ := quotient_surjective N y
    exact ⟨t,(congrArg (original N hN) ht).trans hy⟩
  · exact (hx (Or.inl (Or.inl ⟨c,hc⟩))).elim

variable {M : ℕ}

/-- The same ordered old source that the strict compact-volume
receiver embeds, with its coordinates in their original order. -/
abbrev ordinaryOrderedInclusion (hM : 5 ≤ M)
    (z : Fin g → Base (image M)) : Fin g → Filled M hM :=
  fun j => original M hM (z j)

theorem ordinaryOrderedInclusion_openEmbedding (hM : 5 ≤ M) :
    IsOpenEmbedding (ordinaryOrderedInclusion (g := g) hM) :=
  Topology.IsOpenEmbedding.piMap (f := fun _ : Fin g => original M hM)
    (fun _ => original_openEmbedding M hM)

abbrev fullPeriodToFilled (M g : ℕ) (hM : 5 ≤ M)
    (t : Fin g → UpperHalfPlane) : Fin g → Filled M hM :=
  ordinaryOrderedInclusion hM (fun j => quotientMap M (t j))

def ordinaryCritical (f : Fin g → Form M) : Set (Fin g → UpperHalfPlane) :=
  {t | (periodMatrix f t).det = 0}

private theorem matrix_for_same_period (f : Fin g → Form M) (t : Fin g → UpperHalfPlane) :
    rowMatrix f (fun j => (t j : ℂ)) = periodMatrix f t := by
  unfold periodMatrix
  exact rowMatrix_coe f t

/-- Coincident actual filled coordinates would give proportional
columns in the strict volume donor's matrix, even when their actual
upstairs period lifts are DIFFERENT. The multiplier is the very
same level-M differential cocycle, independent of the row. -/
theorem distinct_filled_of_regular_period (hM : 5 ≤ M) (f : Fin g → Form M)
    (t : Fin g → UpperHalfPlane) (hdet : (periodMatrix f t).det ≠ 0) :
    Injective (fullPeriodToFilled M g hM t) := by
  classical
  intro i j hij
  by_contra hne
  have he : quotientMap M (t i) = quotientMap M (t j) :=
    (original_openEmbedding M hM).injective hij
  have horbit : (MulAction.orbitRel (image M) UpperHalfPlane).r (t i) (t j) :=
    Quotient.exact he
  obtain ⟨γ,hγ⟩ := MulAction.orbitRel_apply.mp horbit
  have hγ' : γ • t j = t i := hγ
  let d : ℂ := derivative (γ : G) (t j)
  let A : Matrix (Fin g) (Fin g) ℂ := periodMatrix f t
  have hcol (r : Fin g) : d * A r i = A r j := by
    have h := differential_pullback (f r) γ (t j)
    rw [hγ'] at h
    change d * f r (t i) = f r (t j)
    exact (mul_comm _ _).trans h
  have hu : A.updateCol j (d • fun r => A r i) = A := by
    apply Matrix.ext
    intro r k
    by_cases hk : k = j
    · subst k
      rw [Matrix.updateCol_self]
      change d * A r i = A r j
      exact hcol r
    · exact Matrix.updateCol_ne hk
  have hsing : A.det = 0 := by
    calc
      A.det = (A.updateCol j (d • fun r => A r i)).det := congrArg Matrix.det hu.symm
      _ = d * (A.updateCol j (fun r => A r i)).det := Matrix.det_updateCol_smul A j d _
      _ = 0 := by rw [Matrix.det_updateCol_eq_zero (M := A) hne,mul_zero]
  exact hdet hsing

variable {J ι : Type}
variable [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]
  [T2Space J] [MeasurableSpace J] [BorelSpace J] [Finite ι]

abbrev goodSource (hM : 5 ≤ M) (f : Fin g → Form M) :
    Set (Fin g → Filled M hM) :=
  (fullPeriodToFilled M g hM '' (ordinaryCritical f)ᶜ) \ orderedDiscarded M hM

abbrev filledOrderedAbel {hM : 5 ≤ M} (a : Filled M hM → J)
    (z : Fin g → Filled M hM) : J :=
  ∑ j : Fin g, a (z j)

/-- Complement of the image of the entire bad compact source, not
the image of only one chosen regular sheet. -/
def goodTarget (hM : 5 ≤ M) (f : Fin g → Form M) (a : Filled M hM → J) : Set J :=
  (filledOrderedAbel (g := g) a '' (goodSource hM f)ᶜ)ᶜ

private theorem actual_periodProduct_isOpenMap (hM : 5 ≤ M) :
    IsOpenMap (fullPeriodToFilled M g hM) := by
  let h : UpperHalfPlane → Filled M hM := original M hM ∘ quotientMap M
  have hO : IsOpenMap h :=
    (original_openEmbedding M hM).isOpenMap.comp (quotient_localHomeomorph M hM).isOpenMap
  refine IsOpenMap.piMap (f := fun _ : Fin g => h) (fun _ => hO) ?_
  exact Filter.eventually_cofinite.mpr (Set.toFinite _)

private theorem criticalComp_isOpen (f : Fin g → Form M) : IsOpen (ordinaryCritical f)ᶜ := by
  have hMtx : Continuous (periodMatrix f) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun t : Fin g → UpperHalfPlane => f i (t j))
    exact (ModularFormClass.continuous (f i)).comp (continuous_apply j)
  let r : (Fin g → UpperHalfPlane) → ℂ := fun t => (periodMatrix f t).det
  have hr : Continuous r := hMtx.matrix_det
  have he : (ordinaryCritical f)ᶜ = r ⁻¹' ({0} : Set ℂ)ᶜ := by
    ext t
    change (¬ r t = 0) ↔ (¬ r t ∈ ({0} : Set ℂ))
    rw [Set.mem_singleton_iff]
  rw [he]
  exact isClosed_singleton.isOpen_compl.preimage hr

private theorem goodSource_open (hM : 5 ≤ M) (f : Fin g → Form M) :
    IsOpen (goodSource hM f) := by
  letI := AllCuspHausdorff318.filled_t2 M hM
  have hQ : IsClosed (orderedDiscarded M (g := g) hM) := by
    unfold orderedDiscarded
    exact isClosed_iUnion_of_finite
      (fun j => (discarded_finite M hM).isClosed.preimage (continuous_apply j))
  exact ((actual_periodProduct_isOpenMap (g := g) hM) _ (criticalComp_isOpen f)).sdiff hQ

/-- Ordinary critical-value nullity on the actual uncut primitive.
Both the critical-image lemma and the passage through the SAME
exponential are already strict donors. No old duplicate Haar
transfer proof or cusp derivative is needed. -/
theorem actual_ordinary_critical_target_null (hM : 5 ≤ M) (f : Fin g → Form M)
    (L : Submodule ℤ (V g)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (q : V g →+ J) (hq : Continuous q) (hqS : Surjective q)
    (hker : ∀ v : V g, q v = 0 ↔ v ∈ L) (C : IdentityChart q)
    (a : Base (image M) → J) (ha : Continuous a)
    (hread : InvariantDifferentialEquation f C a) :
    targetVolume L b (volume : Measure (V g)) q
      ((fun t : Fin g → UpperHalfPlane => ∑ j : Fin g, a (quotientMap M (t j))) ''
        ordinaryCritical f) = 0 := by
  obtain ⟨c,_,hval,hDer⟩ :=
    exists_ordered_lift_from_invariant_differential hM f q hq hqS C a ha hread
  let S : Set (V g) := {x | x ∈ fullPeriods g ∧ (rowMatrix f x).det = 0}
  have hS : (volume : Measure (V g)) (liftSum f c '' S) = 0 := by
    apply SelectedActualAbelExceptionalSetNull318.critical_image_null volume (liftSum f c)
      (fun x => abelLinear (rowMatrix f x)) S
    · exact fun x hx => (hDer x hx.1).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      rw [abelLinear_det]
      exact hx.2
  have hImage := image_null_through_actual_exponential L b q hq hker C _ hS
  apply measure_mono_null _ hImage
  rintro _ ⟨t,ht,rfl⟩
  let x : V g := fun j => (t j : ℂ)
  have hx : x ∈ S := by
    refine ⟨fun j _ => (t j).im_pos,?_⟩
    change (rowMatrix f (fun j => (t j : ℂ))).det = 0
    rw [matrix_for_same_period f t]
    exact ht
  exact ⟨liftSum f c x,⟨x,hx,rfl⟩,hval t⟩

/-- All preimages of this actual open target are ordinary, avoid the
actual discarded points, and have nonzero original determinant and
distinct filled points. The missing same-object geometric input is
the actual degree-one a and its invariant readout, not a chosen J=1
tuple. The factorial count is deliberately not assumed or asserted. -/
theorem actual_good_target_regular_distinct (hM : 5 ≤ M) (f : Fin g → Form M)
    (L : Submodule ℤ (V g)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (q : V g →+ J) (hq : Continuous q) (hqS : Surjective q)
    (hker : ∀ v : V g, q v = 0 ↔ v ∈ L) (C : IdentityChart q)
    (a : Filled M hM → J) (ha : Continuous a)
    (hread : InvariantDifferentialEquation f C (a ∘ original M hM)) :
    IsOpen (goodTarget hM f a) ∧
      targetVolume L b (volume : Measure (V g)) q (goodTarget hM f a)ᶜ = 0 ∧
      ∀ z : Fin g → Filled M hM, filledOrderedAbel a z ∈ goodTarget hM f a →
        ∃ t : Fin g → UpperHalfPlane, fullPeriodToFilled M g hM t = z ∧
          (periodMatrix f t).det ≠ 0 ∧ z ∉ orderedDiscarded M hM ∧ Injective z := by
  classical
  let E := Fin g → Filled M hM
  let A : E → J := filledOrderedAbel a
  let R := goodSource hM f
  let Q := orderedDiscarded M (g := g) hM
  let ν := targetVolume L b (volume : Measure (V g)) q
  have hA : Continuous A := continuous_finsetSum Finset.univ (fun j _ => ha.comp (continuous_apply j))
  letI : CompactSpace (Filled M hM) := AllCuspCompact318.filled_compactSpace M hM
  have hClosed : IsClosed (A '' Rᶜ) := ((goodSource_open hM f).isClosed_compl.isCompact.image hA).isClosed
  refine ⟨hClosed.isOpen_compl,?_,?_⟩
  · have hD : ν (A '' Q) = 0 :=
      discarded_abel_target_null hM f L b q hq hqS hker C (original M hM) a
        (ha.comp (original_openEmbedding M hM).continuous) hread
        (discarded M hM) (discarded_finite M hM).countable
        (outside_discarded_is_period M hM)
    have hCrit : ν ((A ∘ fullPeriodToFilled M g hM) '' ordinaryCritical f) = 0 :=
      actual_ordinary_critical_target_null hM f L b q hq hqS hker C
        (a ∘ original M hM) (ha.comp (original_openEmbedding M hM).continuous) hread
    have hSub : A '' Rᶜ ⊆ (A '' Q) ∪ ((A ∘ fullPeriodToFilled M g hM) '' ordinaryCritical f) := by
      rintro _ ⟨z,hz,rfl⟩
      by_cases hQ : z ∈ Q
      · exact Or.inl ⟨z,hQ,rfl⟩
      · have hLift (j : Fin g) : ∃ t : UpperHalfPlane,
            original M hM (quotientMap M t) = z j := by
          apply outside_discarded_is_period M hM
          intro hBad
          exact hQ (Set.mem_iUnion.mpr ⟨j,hBad⟩)
        choose t ht using hLift
        have he : fullPeriodToFilled M g hM t = z := funext ht
        have htCrit : t ∈ ordinaryCritical f := by
          by_contra hn
          exact hz ⟨⟨t,hn,he⟩,hQ⟩
        exact Or.inr ⟨t,htCrit,congrArg A he⟩
    change ν ((A '' Rᶜ)ᶜ)ᶜ = 0
    rw [compl_compl]
    exact measure_mono_null hSub (measure_union_null hD hCrit)
  · intro z hz
    change A z ∈ (A '' Rᶜ)ᶜ at hz
    have hR : z ∈ R := by
      by_contra hn
      exact hz ⟨z,hn,rfl⟩
    obtain ⟨⟨t,ht,he⟩,hQ⟩ := hR
    have hdet : (periodMatrix f t).det ≠ 0 := ht
    have hi := distinct_filled_of_regular_period hM f t hdet
    have hinj : Injective z := by
      rw [← he]
      exact hi
    exact ⟨t,he,hdet,hQ,hinj⟩

end SelectedActualFilledAbelGoodTargetDistinct318

#print axioms SelectedActualFilledAbelGoodTargetDistinct318.distinct_filled_of_regular_period
#print axioms SelectedActualFilledAbelGoodTargetDistinct318.actual_ordinary_critical_target_null
#print axioms SelectedActualFilledAbelGoodTargetDistinct318.actual_good_target_regular_distinct
