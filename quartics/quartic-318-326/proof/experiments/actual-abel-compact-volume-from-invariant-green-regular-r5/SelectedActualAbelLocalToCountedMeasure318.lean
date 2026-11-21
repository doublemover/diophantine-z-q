module

public import SelectedAbelFiniteSheetMeasure318
public import SelectedActualAbelCountableSheetAtlas318
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal Topology
open SelectedAbelFiniteSheetMeasure318 SelectedActualAbelCountableSheetAtlas318

namespace SelectedActualAbelLocalToCountedMeasure318

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} {V : Set Y}

private theorem open_image_of_localHomeomorphOn
    (hreg : IsLocalHomeomorphOn f (f ⁻¹' V)) (O : Set X) (hO : IsOpen O)
    (hOV : O ⊆ f ⁻¹' V) : IsOpen (f '' O) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨e,he,heq⟩ := hreg x (hOV hx)
  let W := e '' (e.source ∩ O)
  have hW : IsOpen W := e.isOpen_image_source_inter hO
  have hxe : f x = e x := congrFun heq x
  have hxW : f x ∈ W := ⟨x,⟨he,hx⟩,hxe.symm⟩
  have hWO : W ⊆ f '' O := by
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨z,hz.2,congrFun heq z⟩
  exact Filter.mem_of_superset (hW.mem_nhds hxW) hWO

variable [MeasurableSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- The local measure is supplied only near each actual ordinary regular source
point, and its target is the actual image. There is no simultaneous global
atlas/partition or common target patch in the data. -/
def LocalMeasureLaw (f : X → Y) (V : Set Y) (μ : Measure X) (ν : Measure Y) : Prop :=
  ∀ x ∈ f ⁻¹' V, ∃ C : Set X,
    IsOpen C ∧ x ∈ C ∧ InjOn f C ∧ Measure.map f (μ.restrict C) = ν.restrict (f '' C)

private theorem align_measured_patch (d : ℕ) (μ : Measure X) (ν : Measure Y)
    (hf : Continuous f) (hm : Measurable f)
    (hreg : IsLocalHomeomorphOn f (f ⁻¹' V)) (hLocal : LocalMeasureLaw f V μ ν)
    (P : SheetPatch f V d) {y : Y} (hy : y ∈ P.target) :
    ∃ W : Set Y, y ∈ W ∧ IsOpen W ∧ W ⊆ V ∧
      (Measure.map f μ).restrict W = ((d : ℝ≥0∞) • ν).restrict W := by
  classical
  have hcent (i : Fin d) : ∃ x : X, x ∈ P.sheet i ∧ f x = y := by
    have h : y ∈ f '' P.sheet i := by rw [P.sheet_image]; exact hy
    exact h
  choose x hx hxy using hcent
  have hsub (i : Fin d) : P.sheet i ⊆ f ⁻¹' V := by
    intro z hz
    have h : f z ∈ f '' P.sheet i := ⟨z,hz,rfl⟩
    rw [P.sheet_image] at h
    exact P.target_subset h
  unfold LocalMeasureLaw at hLocal
  have hloc (i : Fin d) := hLocal (x i) (hsub i (hx i))
  choose C hCo hxC hCi hCm using hloc
  let O (i : Fin d) := f '' (P.sheet i ∩ C i)
  have hO (i : Fin d) : IsOpen (O i) :=
    open_image_of_localHomeomorphOn hreg _ ((P.sheet_open i).inter (hCo i))
      (fun _ h => hsub i h.1)
  let W := P.target ∩ ⋂ i, O i
  have hW : IsOpen W := P.target_open.inter (isOpen_iInter_of_finite hO)
  have hyW : y ∈ W := ⟨hy,Set.mem_iInter.mpr fun i => ⟨x i,⟨hx i,hxC i⟩,hxy i⟩⟩
  let S (i : Fin d) := f ⁻¹' W ∩ P.sheet i
  have hS (i : Fin d) : MeasurableSet (S i) :=
    ((hW.preimage hf).inter (P.sheet_open i)).measurableSet
  have hdis : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    exact (P.sheet_disjoint hij).mono inter_subset_right inter_subset_right
  have hcov : (⋃ i, S i) = f ⁻¹' W := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact hi.1
    · intro hz
      have htarget : z ∈ f ⁻¹' P.target := hz.1
      have h : z ∈ ⋃ i, P.sheet i := by rw [P.sheet_cover]; exact htarget
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨i,hz,hi⟩
  have hmatch (i : Fin d) : S i = f ⁻¹' W ∩ C i := by
    ext z
    constructor
    · rintro ⟨hz,hzi⟩
      obtain ⟨w,hw,he⟩ := Set.mem_iInter.mp hz.2 i
      have hwz : w = z := P.sheet_inj i hw.1 hzi he
      exact ⟨hz,hwz ▸ hw.2⟩
    · rintro ⟨hz,hzC⟩
      obtain ⟨w,hw,he⟩ := Set.mem_iInter.mp hz.2 i
      have hwz : w = z := hCi i hw.2 hzC he
      exact ⟨hz,hwz ▸ hw.1⟩
  have hsheet (i : Fin d) : Measure.map f (μ.restrict (S i)) = ν.restrict W := by
    have hWsub : W ⊆ f '' C i := by
      intro y hy
      obtain ⟨z,hz,he⟩ := Set.mem_iInter.mp hy.2 i
      exact ⟨z,hz.2,he⟩
    have hfirst : Measure.map f (μ.restrict (S i)) =
        (Measure.map f (μ.restrict (C i))).restrict W := by
      rw [Measure.restrict_map hm hW.measurableSet,
        Measure.restrict_restrict (hm hW.measurableSet),hmatch]
    exact hfirst.trans
      ((congrArg (fun m : Measure Y => m.restrict W) (hCm i)).trans
        (Measure.restrict_restrict_of_subset hWsub))
  exact ⟨W,hyW,hW,fun _ hy => P.target_subset hy.1,
    map_restrict_eq_count hm μ ν hW.measurableSet S hS hdis hcov hsheet⟩

/-- Produce the complete counted pushforward from actual local change of
variables and geometric regular-fibre data. Properness (compact source)
selects exhaustive, not merely injective, sheets. Their given local
coordinate domains are aligned to one shared target patch by uniqueness
on each inverse sheet. No chart family, overlap compatibility, countable
partition, or global integral identity is assumed. -/
theorem map_eq_count_of_local_laws [T2Space X] [CompactSpace X] [T2Space Y]
    [SecondCountableTopology Y] (μ : Measure X) (ν : Measure Y) (d : ℕ) (f : X → Y)
    (hf : Continuous f) (hm : Measurable f) (V : Set Y) (hV : IsOpen V)
    (hreg : IsLocalHomeomorphOn f (f ⁻¹' V))
    (hdegree : ∀ y ∈ V, Nonempty ((f ⁻¹' {y}) ≃ Fin d))
    (hLocal : LocalMeasureLaw f V μ ν)
    (hSnull : μ (f ⁻¹' Vᶜ) = 0) (hTnull : ν Vᶜ = 0) :
    Measure.map f μ = (d : ℝ≥0∞) • ν := by
  classical
  obtain ⟨T,_,P,hP⟩ := countable_sheet_atlas f V d hf hV hreg hdegree
  have hpatch (y : V) :
      ∃ W : Set Y, y.val ∈ W ∧ IsOpen W ∧ W ⊆ V ∧
        (Measure.map f μ).restrict W = ((d : ℝ≥0∞) • ν).restrict W := by
    have hy : y.val ∈ ⋃ t, (P t).target := by rw [hP]; exact y.property
    obtain ⟨t,ht⟩ := Set.mem_iUnion.mp hy
    exact align_measured_patch d μ ν hf hm hreg hLocal (P t) ht
  choose W hyW hW hWV hcount using hpatch
  have hsub : V ⊆ ⋃ y : V, W y := fun y hy => Set.mem_iUnion.mpr ⟨⟨y,hy⟩,hyW ⟨y,hy⟩⟩
  obtain ⟨I,hI,hcov⟩ :=
    (HereditarilyLindelofSpace.isLindelof V).elim_countable_subcover W hW hsub
  letI : Countable I := hI.to_subtype
  have hUnion : (⋃ i : I, W i.val) = V := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hy
      exact hWV i.val hi
    · intro y hy
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcov hy)
      obtain ⟨hiI,hyW⟩ := Set.mem_iUnion.mp hi
      exact Set.mem_iUnion.mpr ⟨⟨i,hiI⟩,hyW⟩
  have hrestrict :
      (Measure.map f μ).restrict V = ((d : ℝ≥0∞) • ν).restrict V := by
    rw [← hUnion]
    exact (Measure.restrict_iUnion_congr (s := fun i : I => W i.val)).mpr (fun i => hcount i.val)
  have hmAE : ∀ᵐ y ∂(Measure.map f μ), y ∈ V := by
    rw [ae_iff]
    change (Measure.map f μ) Vᶜ = 0
    rw [Measure.map_apply hm hV.measurableSet.compl]
    exact hSnull
  have hnAE : ∀ᵐ y ∂((d : ℝ≥0∞) • ν), y ∈ V := by
    rw [ae_iff]
    change ((d : ℝ≥0∞) • ν) Vᶜ = 0
    rw [Measure.smul_apply,hTnull,smul_zero]
  exact (Measure.restrict_eq_self_of_ae_mem hmAE).symm.trans
    (hrestrict.trans (Measure.restrict_eq_self_of_ae_mem hnAE))

end SelectedActualAbelLocalToCountedMeasure318

#print axioms SelectedActualAbelLocalToCountedMeasure318.map_eq_count_of_local_laws
