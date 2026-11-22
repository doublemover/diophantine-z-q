module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Group.FundamentalDomain

public section

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped Pointwise

namespace SelectedActualAbelTargetLatticeHaar318

variable {E T ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [AddCommGroup T] [MeasurableSpace T]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [Finite ι]

/-- The stock half-open fundamental box, in the same actual full lattice. -/
def latticeBox (b : Module.Basis ι ℤ L) : Set E :=
  ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)

/-- Unnormalized target volume from the actual exponential, without a Haar
probability factor or an independent target volume instance. -/
def targetVolume (b : Module.Basis ι ℤ L) (μ : Measure E) (q : E →+ T) : Measure T :=
  (μ.restrict (latticeBox L b)).map q

private theorem fibers_eq (q : E →+ T)
    (hker : ∀ v : E, q v = 0 ↔ v ∈ L) (x y : E) :
    q x = q y ↔ ∃ n : L, n +ᵥ y = x := by
  constructor
  · intro h
    have hm : q (x-y) = 0 := by rw [map_sub, h, sub_self]
    refine ⟨⟨x-y,(hker _).mp hm⟩, ?_⟩
    change x-y+y = x
    exact sub_add_cancel x y
  · rintro ⟨n,hn⟩
    have he : (n : E)+y=x := hn
    have h₀ : q (n : E) = 0 := (hker _).mpr n.property
    rw [← he, map_add, h₀, zero_add]

/-- The restriction of the *constructed* target volume to an injective
actual logarithm chart is precisely reference Haar measure pushed from
that chart. The quotient is the actual map q with the actual kernel L. -/
theorem targetVolume_restrict_chart (b : Module.Basis ι ℤ L) (μ : Measure E)
    [Measure.IsAddHaarMeasure μ] (q : E →+ T) (hq : Measurable q)
    (hker : ∀ v : E, q v = 0 ↔ v ∈ L)
    (B : Set E) (hB : MeasurableSet B) (hBi : Set.InjOn q B)
    (hW : MeasurableSet (q '' B)) :
    (targetVolume L b μ q).restrict (q '' B) = (μ.restrict B).map q := by
  classical
  letI : MeasurableVAdd L E :=
    (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  letI : VAddInvariantMeasure L E μ :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  let P : Set E := latticeBox L b
  have hP : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet (b.ofZLatticeBasis ℝ)
  have hPD : IsAddFundamentalDomain L P μ := ZLattice.isAddFundamentalDomain b μ
  ext1 U hU
  let H : Set E := q ⁻¹' U ∩ B
  let W : L → Set E := fun n => (n +ᵥ H) ∩ P
  have hH : MeasurableSet H := (hq hU).inter hB
  have hWm (n : L) : MeasurableSet (W n) :=
    ((measurableEmbedding_const_vadd n).measurableSet_image.mpr hH).inter hP
  have hWi : Pairwise (fun n m => Disjoint (W n) (W m)) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun x hx hn => hnm ?_
    obtain ⟨a,ha,hax⟩ := Set.mem_vadd_set.mp hx.1
    obtain ⟨a',ha',ha'x⟩ := Set.mem_vadd_set.mp hn.1
    have haq : q x = q a := (fibers_eq L q hker x a).mpr ⟨n,hax⟩
    have ha'q : q x = q a' := (fibers_eq L q hker x a').mpr ⟨m,ha'x⟩
    have haa' : a = a' := hBi ha.2 ha'.2 (haq.symm.trans ha'q)
    subst a'
    have h : (n : E) + a = (m : E) + a := hax.trans ha'x.symm
    exact Subtype.ext (add_right_cancel h)
  have hcover : (⋃ n, W n) = q ⁻¹' (U ∩ q '' B) ∩ P := by
    ext x
    constructor
    · intro hx
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a,ha,hax⟩ := Set.mem_vadd_set.mp hn.1
      have he : q x = q a := (fibers_eq L q hker x a).mpr ⟨n,hax⟩
      exact ⟨⟨he.symm ▸ ha.1,⟨a,ha.2,he.symm⟩⟩,hn.2⟩
    · intro hx
      obtain ⟨a,ha,haq⟩ := hx.1.2
      obtain ⟨n,hn⟩ := (fibers_eq L q hker x a).mp haq.symm
      have haU : q a ∈ U := haq.symm ▸ hx.1.1
      exact Set.mem_iUnion.mpr ⟨n,Set.mem_vadd_set.mpr ⟨a,⟨haU,ha⟩,hn⟩,hx.2⟩
  change ((μ.restrict P).map q).restrict (q '' B) U = (μ.restrict B).map q U
  rw [Measure.restrict_apply hU, Measure.map_apply hq (hU.inter hW),
    Measure.restrict_apply (hq (hU.inter hW)), Measure.map_apply hq hU,
    Measure.restrict_apply (hq hU), ← hcover, measure_iUnion hWi hWm]
  exact (hPD.measure_eq_tsum H).symm

/-- The total true target volume, in the given real frame, is precisely the
covolume of the actual lattice. This is not a Haar probability measure. -/
theorem targetVolume_mass (b : Module.Basis ι ℤ L) (μ : Measure E)
    [Measure.IsAddHaarMeasure μ] (q : E →+ T) (hq : Measurable q) :
    ((targetVolume L b μ q) Set.univ).toReal = ZLattice.covolume L μ := by
  change (((μ.restrict (latticeBox L b)).map q) Set.univ).toReal =
    ZLattice.covolume L μ
  rw [Measure.map_apply hq MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
  exact (ZLattice.covolume_eq_measure_fundamentalDomain L μ
    (ZLattice.isAddFundamentalDomain b μ)).symm

end SelectedActualAbelTargetLatticeHaar318

#print axioms SelectedActualAbelTargetLatticeHaar318.targetVolume_restrict_chart
#print axioms SelectedActualAbelTargetLatticeHaar318.targetVolume_mass
