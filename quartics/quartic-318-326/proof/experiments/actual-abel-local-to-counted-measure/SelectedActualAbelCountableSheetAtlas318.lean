module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section

open Set

namespace SelectedActualAbelCountableSheetAtlas318

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- An enumerated set of actual inverse sheets over one open target patch. -/
structure SheetPatch (f : E → X) (V : Set X) (d : ℕ) where
  target : Set X
  sheet : Fin d → Set E
  target_open : IsOpen target
  target_subset : target ⊆ V
  sheet_open : ∀ j, IsOpen (sheet j)
  sheet_cover : (⋃ j, sheet j) = f ⁻¹' target
  sheet_disjoint : Pairwise (fun i j => Disjoint (sheet i) (sheet j))
  sheet_image : ∀ j, f '' sheet j = target
  sheet_inj : ∀ j, Set.InjOn f (sheet j)

private theorem patch_of_evenlyCovered {f : E → X} {V : Set X} {y : X} {d : ℕ}
    (hf : Continuous f) (hV : IsOpen V) (hy : y ∈ V)
    (h : IsEvenlyCovered f y (f ⁻¹' {y}))
    (e : (f ⁻¹' {y}) ≃ Fin d) :
    ∃ P : SheetPatch f V d, y ∈ P.target := by
  classical
  obtain ⟨hdis, U, hyU, hU, hfU, H, hH⟩ := h
  letI : DiscreteTopology (f ⁻¹' {y}) := hdis
  let W : Set X := U ∩ V
  let C (i : Fin d) : Set (f ⁻¹' U) :=
    (fun z : f ⁻¹' U => (H z).2) ⁻¹' {e.symm i}
  let S (i : Fin d) : Set E :=
    Subtype.val '' C i ∩ f ⁻¹' V
  have hC (i : Fin d) : IsOpen (C i) :=
    (isOpen_discrete _).preimage (continuous_snd.comp H.continuous)
  have hS (i : Fin d) : IsOpen (S i) :=
    (hfU.isOpenMap_subtype_val _ (hC i)).inter (hV.preimage hf)
  have membership (i : Fin d) (z : E) :
      z ∈ S i ↔ ∃ hz : f z ∈ U, (H ⟨z, hz⟩).2 = e.symm i ∧ f z ∈ V := by
    constructor
    · rintro ⟨⟨⟨w, hw⟩, hCw, rfl⟩, hv⟩
      exact ⟨hw, hCw, hv⟩
    · rintro ⟨hz, hz₂, hv⟩
      exact ⟨⟨⟨z, hz⟩, hz₂, rfl⟩, hv⟩
  refine ⟨⟨W, S, hU.inter hV, fun _ hz => hz.2, hS, ?_, ?_, ?_, ?_⟩, ⟨hyU, hy⟩⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hu, _, hv⟩ := (membership i z).mp hi
      exact ⟨hu, hv⟩
    · intro hz
      have hu : f z ∈ U := hz.1
      let b : f ⁻¹' {y} := (H ⟨z, hu⟩).2
      exact Set.mem_iUnion.mpr ⟨e b, (membership (e b) z).mpr
        ⟨hu, (e.symm_apply_apply b).symm, hz.2⟩⟩
  · intro i j hij
    refine Set.disjoint_left.mpr fun z hi hj => hij (e.symm.injective ?_)
    obtain ⟨hiU, hi₂, _⟩ := (membership i z).mp hi
    obtain ⟨hjU, hj₂, _⟩ := (membership j z).mp hj
    exact hi₂.symm.trans hj₂
  · intro i
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hu, _, hv⟩ := (membership i z).mp hz
      exact ⟨hu, hv⟩
    · intro hx
      let z : f ⁻¹' U := H.symm (⟨x, hx.1⟩, e.symm i)
      have hHz : H z = (⟨x, hx.1⟩, e.symm i) := H.apply_symm_apply _
      have hz₁ : f z.val = x :=
        (hH z).symm.trans (congrArg (fun k : U × (f ⁻¹' {y}) => k.1.val) hHz)
      have hz₂ : (H z).2 = e.symm i := congrArg Prod.snd hHz
      have hzV : f z.val ∈ V := hz₁.symm ▸ hx.2
      exact ⟨z.val, (membership i z.val).mpr ⟨z.property, hz₂, hzV⟩, hz₁⟩
  · intro i x hx z hz hxz
    obtain ⟨hxU, hx₂, _⟩ := (membership i x).mp hx
    obtain ⟨hzU, hz₂, _⟩ := (membership i z).mp hz
    have hfirst : (H ⟨x, hxU⟩).1 = (H ⟨z, hzU⟩).1 :=
      Subtype.ext ((hH ⟨x, hxU⟩).trans (hxz.trans (hH ⟨z, hzU⟩).symm))
    have hsecond : (H ⟨x, hxU⟩).2 = (H ⟨z, hzU⟩).2 := hx₂.trans hz₂.symm
    exact congrArg Subtype.val (H.injective (Prod.ext hfirst hsecond))

/-- A single proper source produces a countable family of exhaustive actual sheets on its
regular-value open. No separately specified topological sheet partition is an input.

For the actual ordered Abel map take E to be the compact product and V the complement
of the critical and discarded-coordinate images. The finite fibre input is literal;
this step does not assume regularity at any given arithmetic center. -/
theorem countable_sheet_atlas [T2Space E] [CompactSpace E] [T2Space X]
    [SecondCountableTopology X] (f : E → X) (V : Set X) (d : ℕ)
    (hf : Continuous f) (hV : IsOpen V)
    (hreg : IsLocalHomeomorphOn f (f ⁻¹' V))
    (hdegree : ∀ y ∈ V, Nonempty ((f ⁻¹' {y}) ≃ Fin d)) :
    ∃ T : Set V, T.Countable ∧ ∃ P : T → SheetPatch f V d,
      (⋃ a, (P a).target) = V := by
  classical
  have hcover : IsCoveringMapOn f V := IsCoveringMapOn.of_isLocalHomeomorphOn hf hreg
  have hpatch (a : V) : ∃ P : SheetPatch f V d, a.val ∈ P.target :=
    patch_of_evenlyCovered hf hV a.property (hcover a.val a.property)
      (Classical.choice (hdegree a.val a.property))
  choose P hP using hpatch
  have hsub : V ⊆ ⋃ a : V, (P a).target :=
    fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hP ⟨y, hy⟩⟩
  have hL : IsLindelof V := HereditarilyLindelofSpace.isLindelof V
  obtain ⟨T, hT, hTU⟩ :=
    hL.elim_countable_subcover (fun a : V => (P a).target)
      (fun a => (P a).target_open) hsub
  refine ⟨T, hT, fun a => P a.val, Set.Subset.antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
    exact (P a.val).target_subset ha
  · intro y hy
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hTU hy)
    obtain ⟨hat, hay⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨⟨a, hat⟩, hay⟩

end SelectedActualAbelCountableSheetAtlas318
