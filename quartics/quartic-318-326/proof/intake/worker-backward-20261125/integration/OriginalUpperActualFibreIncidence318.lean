module
public import OriginalUpperActualFibreComponents318
public import Mathlib.Topology.KrullDimension

public section
noncomputable section
namespace OriginalUpperActualFibreIncidence318

open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open OriginalUpperActualFibreComponents318
attribute [local instance] specializationOrder

universe u
variable {X Z : Scheme.{u}} [IsIntegral X] (s : X ⟶ Z) (p : Z)
variable (E F : C s p) (different : E ≠ F)
variable (closed : IsClosed ({p} : Set Z))
variable (vertical : s (genericPoint X) ≠ p)
variable (dim : ∀ x : X, coheight x ≤ 2)

/-- Actual meeting points in the original ambient arithmetic surface. -/
abbrev common : Set X :=
  (ambientSupport s p E : Set X) ∩ (ambientSupport s p F : Set X)

theorem ambientGeneric_over : s (ambientGeneric s p E) = p := by
  have h := Set.mem_range_self (f := s.fiberι p) (fibreGeneric s p E)
  rw [s.range_fiberι p] at h
  exact h

include different in
theorem fibre_generic_not_other :
    fibreGeneric s p E ∉ (F : Set (s.fiber p)) := by
  intro h
  have sub : (E : Set (s.fiber p)) ⊆ F := by
    intro x hx
    exact ((genericPoints.isGenericPoint_ofComponent E).specializes hx).mem_closed
      (isClosed_of_mem_irreducibleComponents _ F.property) h
  have rev : (F : Set (s.fiber p)) ⊆ E := E.property.2 F.property.1 sub
  exact different (Subtype.ext (sub.antisymm rev))

include different closed in
theorem ambient_generic_not_other :
    ambientGeneric s p E ∉ ambientSupport s p F := by
  intro h
  have h' : ambientGeneric s p E ∈ s.fiberι p '' (F : Set (s.fiber p)) := by
    rw [← support_image s p closed F]
    exact h
  obtain ⟨v,hv,he⟩ := h'
  have e : v = fibreGeneric s p E := (s.fiberι p).isEmbedding.injective he
  exact fibre_generic_not_other s p E F different (by simpa only [e] using hv)

private theorem raises {x y : X} (sp : x ⤳ y) (neq : x ≠ y)
    (n : ℕ∞) (hle : n ≤ coheight x) :
    n + 1 ≤ coheight y := by
  have lt : y < x := lt_of_le_of_ne sp (Ne.symm neq)
  have hmono : n + 1 ≤ coheight x + 1 := add_le_add hle (le_refl (1 : ℕ∞))
  exact hmono.trans (Order.coheight_add_one_le lt)

include vertical in
theorem generic_positive : 1 ≤ coheight (ambientGeneric s p E) := by
  have e : genericPoint X ≠ ambientGeneric s p E := by
    intro h
    exact vertical ((congrArg (fun y : X => s y) h).trans (ambientGeneric_over s p E))
  have hg : genericPoint X ⤳ ambientGeneric s p E := genericPoint_specializes _
  have hz : (0 : ℕ∞) + 1 ≤ coheight (ambientGeneric s p E) := raises hg e 0 zero_le
  simpa only [zero_add] using hz

/-- Read the true generization from the represented ordinary stalk. -/
private theorem specializes_from_component {x : X} (hx : x ∈ ambientSupport s p E) :
    ambientGeneric s p E ⤳ x := by
  have hm : ambientGeneric s p E ∈ Set.range (X.fromSpecStalk x) :=
    ⟨pointAt s p E x hx, pointAt_reads s p E x hx⟩
  rw [Scheme.range_fromSpecStalk] at hm
  exact hm

include closed vertical different dim in
/-- At a distinct-component meeting, the actual named component's
ambient generic point has coheight one. The proof uses the real
specialization chain between the surface generic and the meeting point. -/
theorem generic_height_one (x : X) (hx : x ∈ common s p E F) :
    coheight (ambientGeneric s p E) = 1 := by
  have hsp : ambientGeneric s p E ⤳ x := specializes_from_component s p E hx.1
  have neq : ambientGeneric s p E ≠ x := by
    intro e
    apply ambient_generic_not_other s p E F different closed
    rw [e]
    exact hx.2
  have upper := (raises hsp neq _ le_rfl).trans (dim x)
  refine le_antisymm ?_ (generic_positive s p E vertical)
  exact (ENat.add_le_add_iff_right (by decide : (1:ℕ∞) ≠ ⊤)).mp
    (show coheight (ambientGeneric s p E) + 1 ≤ 1 + 1 from upper)

include closed vertical different dim in
theorem no_strict_specialization_on_common {x y : X}
    (hx : x ∈ common s p E F) (sp : x ⤳ y) : x = y := by
  by_contra ne
  have gne : ambientGeneric s p E ≠ x := by
    intro e
    apply ambient_generic_not_other s p E F different closed
    rw [e]
    exact hx.2
  have lo : (2:ℕ∞) ≤ coheight x :=
    raises (specializes_from_component s p E hx.1) gne 1 (generic_positive s p E vertical)
  have impossible : (3:ℕ∞) ≤ 2 := (raises sp ne 2 lo).trans (dim y)
  exact (by decide : ¬ (3:ℕ∞) ≤ 2) impossible

variable [NoetherianSpace X]

include closed vertical different dim in
/-- Finiteness of the literal meeting points, not a supplied finite
graph edge list. Every closed irreducible subset of this intersection
is a singleton by sobriety and the absence of strict specialization. -/
theorem finite_common : (common s p E F).Finite := by
  obtain ⟨W,hW,hClosed,hIrred,hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible
      ((ambientSupport s p E).isClosed.inter (ambientSupport s p F).isClosed)
  rw [hcover]
  refine hW.sUnion ?_
  intro U hU
  let x := (hIrred U hU).genericPoint
  have gx : IsGenericPoint x U := (hIrred U hU).isGenericPoint_genericPoint (hClosed U hU)
  have hx : x ∈ common s p E F := hcover ▸ Set.mem_sUnion_of_mem gx.mem hU
  have hU' : U ⊆ ({x}:Set X) := by
    intro y hy
    exact Set.mem_singleton_iff.mpr
      (no_strict_specialization_on_common s p E F different closed vertical dim hx
        (gx.specializes hy)).symm
  exact (Set.finite_singleton x).subset hU'

end OriginalUpperActualFibreIncidence318

#print axioms OriginalUpperActualFibreIncidence318.ambient_generic_not_other
#print axioms OriginalUpperActualFibreIncidence318.generic_height_one
#print axioms OriginalUpperActualFibreIncidence318.finite_common
