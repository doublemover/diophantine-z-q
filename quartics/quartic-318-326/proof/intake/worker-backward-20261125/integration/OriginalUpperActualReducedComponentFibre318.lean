module
public import OriginalUpperActualFibreComponents318
public import Mathlib.RingTheory.Localization.Ideal

public section
noncomputable section
namespace OriginalUpperActualReducedComponentFibre318

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open OriginalUpperActualFibreComponents318 (C ambientSupport ambientIdeal ambientGeneric fibreGeneric pointAt pointAt_reads image_in_closure)

universe u
variable {X Z : Scheme.{u}} (s : X ⟶ Z) (p : Z)

theorem closed_union :
    (⨆ E : C s p, ambientSupport s p E) =
      (Closeds.closure (Set.range (s.fiberι p)) : Closeds X) := by
  apply le_antisymm
  · refine iSup_le fun E => ?_
    intro x hx
    have hx' : ambientGeneric s p E ∈ Set.range (X.fromSpecStalk x) :=
      ⟨pointAt s p E x hx, pointAt_reads s p E x hx⟩
    rw [Scheme.range_fromSpecStalk] at hx'
    have sp : ambientGeneric s p E ⤳ x := hx'
    have hg : ambientGeneric s p E ∈ Set.range (s.fiberι p) :=
      Set.mem_range_self (f := s.fiberι p) (fibreGeneric s p E)
    exact sp.mem_closed (Closeds.closure (Set.range (s.fiberι p))).isClosed
      (Closeds.mem_closure.mpr (subset_closure hg))
  · refine Closeds.closure_le.mpr ?_
    rintro _ ⟨v,rfl⟩
    let E : C s p := ⟨irreducibleComponent v,irreducibleComponent_mem_irreducibleComponents v⟩
    exact (le_iSup (ambientSupport s p) E) (image_in_closure s p E
      ⟨v,mem_irreducibleComponent,rfl⟩)

variable [IsReduced (s.fiber p)]

/-- The scheme-theoretic fibre ideal is the intersection of the
actual embedded reduced component ideals. This uses genuine reducedness,
not reducedness of the underlying set or an artificial graph. -/
theorem literal_fibre_ideal :
    (s.fiberι p).ker = ⨅ E : C s p, ambientIdeal s p E := by
  have h := map_vanishingIdeal (s.fiberι p) (⊤ : Closeds (s.fiber p))
  rw [vanishingIdeal_top, Scheme.nilradical_eq_bot, map_bot, Closeds.coe_top, Set.image_univ] at h
  simpa only [← closed_union s p, vanishingIdeal_iSup, ambientIdeal] using h

variable [NoetherianSpace (s.fiber p)]

/-- The equality is an identity of ideals on every literal affine
chart, retaining the represented fibre immersion's kernel. -/
theorem on_affine (U : X.affineOpens) :
    (s.fiberι p).ker.ideal U = ⨅ E : C s p, (ambientIdeal s p E).ideal U := by
  letI : Fintype (C s p) :=
    (NoetherianSpace.finite_irreducibleComponents (α := s.fiber p)).fintype
  rw [literal_fibre_ideal s p, ideal_iInf, iInf_apply]

end OriginalUpperActualReducedComponentFibre318

#print axioms OriginalUpperActualReducedComponentFibre318.closed_union
#print axioms OriginalUpperActualReducedComponentFibre318.literal_fibre_ideal
#print axioms OriginalUpperActualReducedComponentFibre318.on_affine
