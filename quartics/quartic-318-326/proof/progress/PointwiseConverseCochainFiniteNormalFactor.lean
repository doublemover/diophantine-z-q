module
public import PointwiseConverseRawMatrixReceiver
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Order.Filter.Finite
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Compactness.Compact

public section

open Set
open scoped Topology
open PointwiseConverseRawMatrixReceiver

namespace PointwiseConverseCochainFiniteNormalFactor

/-- A fixed finite basis can be bundled before taking the quotient. -/
theorem locallyConstant_of_finite_pi {X J : Type*} [TopologicalSpace X] [Finite J]
    {Y : J → Type*} (f : X → ((j : J) → Y j))
    (hf : ∀ j, IsLocallyConstant (fun x => f x j)) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).2
  intro x
  have h : ∀ᶠ y in 𝓝 x, ∀ j, f y j = f x j :=
    Filter.eventually_all.mpr (fun j => (hf j).eventually_eq x)
  exact h.mono (fun _ hy => funext hy)

theorem locallyConstant_raw_packet {X : Type*} [TopologicalSpace X]
    (S : Shape) (i : ℕ) (f : X → Packet S i)
    (hf : ∀ m a b d, IsLocallyConstant (fun x => f x m a b d)) :
    IsLocallyConstant f := by
  apply locallyConstant_of_finite_pi f
  intro m
  apply locallyConstant_of_finite_pi (fun x => f x m)
  intro a
  apply locallyConstant_of_finite_pi (fun x => f x m a)
  intro b
  exact locallyConstant_of_finite_pi (fun x => f x m a b) (hf m a b)

section Group

variable {G Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Compactness makes local constancy uniform over both original arguments.
Only the source is topological: no topology on the packet type is needed. -/
theorem exists_open_left_preserving [CompactSpace G] (f : LocallyConstant (G × G) Y) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧
      ∀ g h u v : G, u ∈ W → v ∈ W → f (u * g, v * h) = f (g, h) := by
  let E : Set ((G × G) × (G × G)) := {q | f (q.2 * q.1) = f q.1}
  have hE : IsOpen E :=
    ((f.isLocallyConstant.comp_continuous (continuous_snd.mul continuous_fst)).prodMk
      (f.isLocallyConstant.comp_continuous continuous_fst)) (Set.diagonal Y)
  have hEone : (Set.univ : Set (G × G)) ×ˢ ({1} : Set (G × G)) ⊆ E := by
    rintro ⟨g, u⟩ hu
    have he : u = 1 := Set.mem_singleton_iff.mp hu.2
    change f (u * g) = f g
    rw [he, one_mul]
  obtain ⟨U, V, _, hV, hUone, hVone, hUV⟩ :=
    generalized_tube_lemma (isCompact_univ : IsCompact (Set.univ : Set (G × G)))
      (isCompact_singleton : IsCompact ({1} : Set (G × G))) hE hEone
  have hleft : Continuous (fun u : G => (u, (1 : G))) :=
    continuous_id.prodMk continuous_const
  have hright : Continuous (fun v : G => ((1 : G), v)) :=
    continuous_const.prodMk continuous_id
  let W : Set G := (fun u : G => (u, (1 : G))) ⁻¹' V ∩
    (fun v : G => ((1 : G), v)) ⁻¹' V
  have h1V : (1 : G × G) ∈ V := hVone (Set.mem_singleton _)
  have h1W : (1 : G) ∈ W := ⟨h1V, h1V⟩
  have hstep (g u : G × G) (hu : u ∈ V) : f (u * g) = f g :=
    hUV (show (g, u) ∈ U ×ˢ V from ⟨hUone (Set.mem_univ g), hu⟩)
  refine ⟨W, (hV.preimage hleft).inter (hV.preimage hright), h1W, ?_⟩
  intro g h u v hu hv
  calc
    f (u * g, v * h) = f (g, v * h) := by
      simpa only [Prod.mk_mul_mk, one_mul] using hstep (g, v * h) (u, 1) hu.1
    _ = f (g, h) := by
      simpa only [Prod.mk_mul_mk, one_mul] using hstep (g, h) (1, v) hv.2

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The same normal subgroup controls both arguments. This is not a
conjugacy-invariance hypothesis on the original cochains. -/
theorem factor_of_left_preserving (N : Subgroup G) [N.Normal] (f : G × G → Y)
    (hN : ∀ g h u v : G, u ∈ N → v ∈ N → f (u * g, v * h) = f (g, h)) :
    ∃ fbar : (G ⧸ N) → (G ⧸ N) → Y,
      ∀ g h : G, fbar (g : G ⧸ N) (h : G ⧸ N) = f (g, h) := by
  have hfiber (x y g h : G) (hx : (x : G ⧸ N) = g) (hy : (y : G ⧸ N) = h) :
      f (x, y) = f (g, h) := by
    have hxN : x / g ∈ N := QuotientGroup.eq_iff_div_mem.mp hx
    have hyN : y / h ∈ N := QuotientGroup.eq_iff_div_mem.mp hy
    simpa [div_eq_mul_inv, mul_assoc] using hN g h (x / g) (y / h) hxN hyN
  refine ⟨fun x y => f (x.out, y.out), ?_⟩
  intro g h
  exact hfiber (g : G ⧸ N).out (h : G ⧸ N).out g h
    (QuotientGroup.out_eq' (g : G ⧸ N)) (QuotientGroup.out_eq' (h : G ⧸ N))

theorem factor_open_normal [CompactSpace G] [ZeroDimensionalSpace G]
    (f : LocallyConstant (G × G) Y) :
    ∃ N : OpenNormalSubgroup G, Finite (G ⧸ N.toSubgroup) ∧
      ∃ fbar : (G ⧸ N.toSubgroup) → (G ⧸ N.toSubgroup) → Y,
        ∀ g h : G, fbar (g : G ⧸ N.toSubgroup) (h : G ⧸ N.toSubgroup) = f (g, h) := by
  obtain ⟨W, hW, h1, hInv⟩ := exists_open_left_preserving f
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1
  refine ⟨N, Subgroup.quotient_finite_of_isOpen N.toSubgroup N.toOpenSubgroup.isOpen, ?_⟩
  exact factor_of_left_preserving N.toSubgroup f
    (fun g h u v hu hv => hInv g h u v (hN hu) (hN hv))

end Group

section Galois

variable {K Ω Y : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Krull-topology version: the quotient comes from one actual finite Galois
intermediate field, rather than an arbitrary finite set partition. -/
theorem factor_finite_galois (f : LocallyConstant (Gal(Ω/K) × Gal(Ω/K)) Y) :
    ∃ E : FiniteGaloisIntermediateField K Ω, Finite (Gal(Ω/K) ⧸ E.fixingSubgroup) ∧
      ∃ fbar : (Gal(Ω/K) ⧸ E.fixingSubgroup) → (Gal(Ω/K) ⧸ E.fixingSubgroup) → Y,
        ∀ g h : Gal(Ω/K), fbar (g : Gal(Ω/K) ⧸ E.fixingSubgroup)
          (h : Gal(Ω/K) ⧸ E.fixingSubgroup) = f (g, h) := by
  obtain ⟨W, hW, h1, hInv⟩ := exists_open_left_preserving f
  obtain ⟨E, hE⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois W).mp (hW.mem_nhds h1)
  have hOpen : IsOpen (E.fixingSubgroup : Set Gal(Ω/K)) :=
    E.toIntermediateField.fixingSubgroup_isOpen
  refine ⟨E, Subgroup.quotient_finite_of_isOpen E.fixingSubgroup hOpen, ?_⟩
  exact factor_of_left_preserving E.fixingSubgroup f
    (fun g h u v hu hv => hInv g h u v (hE hu) (hE hv))

/-- Instantiation for the fixed retained basis and one Artin precision.
Local constancy of each actual entry is input, not generated by finiteness. -/
theorem raw_packet_factors_finite_galois (S : Shape) (i : ℕ)
    (f : (Gal(Ω/K) × Gal(Ω/K)) → Packet S i)
    (hf : ∀ m a b d, IsLocallyConstant (fun x => f x m a b d)) :
    ∃ E : FiniteGaloisIntermediateField K Ω, Finite (Gal(Ω/K) ⧸ E.fixingSubgroup) ∧
      ∃ fbar : (Gal(Ω/K) ⧸ E.fixingSubgroup) → (Gal(Ω/K) ⧸ E.fixingSubgroup) → Packet S i,
        ∀ g h : Gal(Ω/K), fbar (g : Gal(Ω/K) ⧸ E.fixingSubgroup)
          (h : Gal(Ω/K) ⧸ E.fixingSubgroup) = f (g, h) :=
  factor_finite_galois ⟨f, locallyConstant_raw_packet S i f hf⟩

end Galois

end PointwiseConverseCochainFiniteNormalFactor
