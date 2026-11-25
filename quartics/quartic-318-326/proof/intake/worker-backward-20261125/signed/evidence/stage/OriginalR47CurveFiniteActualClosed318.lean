module
public import OriginalR47ActualFibreNoetherian318
public import OriginalR47ProperBadSupport318
public import Mathlib.Topology.Sober
public section
noncomputable section

namespace OriginalR47CurveFiniteActualClosed318

open AlgebraicGeometry CategoryTheory Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A closed set consisting of closed points of a Noetherian sober
space is finite. Use actual irreducible components of that closed
set, with their generic points, without requiring a dimension
certificate for the ambient fibre. -/
theorem finite {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    (D : Set X) (hD : IsClosed D) (hpt : ∀ x ∈ D, IsClosed ({x} : Set X)) :
    D.Finite := by
  obtain ⟨L,hf,hc,hi,h⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hD
  rw [h]
  apply hf.sUnion
  intro C hC
  obtain ⟨x,hx⟩ := QuasiSober.sober (hi C hC) (hc C hC)
  have hxd : x ∈ D := h.symm ▸ Set.mem_sUnion_of_mem hx.mem hC
  have he : ({x} : Set X) = C := (hpt x hxd).closure_eq.symm.trans hx.closure_eq
  rw [← he]
  exact Set.finite_singleton _

universe u
variable {R : Type u} [CommRing R] [IsDedekindDomain R]
local notation "S" => Spec (CommRingCat.of R)
variable {X : Scheme.{u}} (s : X ⟶ S) [IsProper s]

/-- For the original proper arithmetic model, the actual closed
nodal-point read supplies finite vertical support. The proof
takes no separately entered fibre dimension, enumeration, or
component generic-locus theorem. -/
theorem support (D : Set X) (hD : IsClosed D)
    (vertical : ∀ x ∈ D, s x ≠ genericPoint S)
    (hpt : ∀ x ∈ D, IsClosed ({x} : Set X)) : D.Finite := by
  have H (t : S) : ((s.fiberι t) ⁻¹' D).Finite := by
    letI : NoetherianSpace (s.fiber t) := OriginalR47ActualFibreNoetherian318.actual s t
    refine finite _ (hD.preimage (s.fiberι t).continuous) fun v hv => ?_
    have he : ((s.fiberι t) ⁻¹' {s.fiberι t v}) = ({v} : Set (s.fiber t)) := by
      ext u
      change s.fiberι t u ∈ ({s.fiberι t v} : Set X) ↔ _
      simp only [Set.mem_singleton_iff,(s.fiberι t).isEmbedding.injective.eq_iff]
    rw [← he]
    exact (hpt (s.fiberι t v) hv).preimage (s.fiberι t).continuous
  exact OriginalR47ProperBadSupport318.finite_support s D hD vertical H

end OriginalR47CurveFiniteActualClosed318

#print axioms OriginalR47CurveFiniteActualClosed318.finite
#print axioms OriginalR47CurveFiniteActualClosed318.support
