module
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public section
noncomputable section

namespace CTFieldPrimitiveBoundary318

open CategoryTheory groupCohomology

abbrev GalQ := Field.absoluteGaloisGroup ℚ
abbrev GmRep : Rep ℤ GalQ := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)

/-- The primitives must be continuous for the units with discrete
topology. This is not the whole abstract group-cochain object. -/
@[expose] def continuousTwo :
    AddSubgroup ((Fin 2 → GalQ) → GmRep) where
  carrier := {e | IsLocallyConstant e}
  zero_mem' := IsLocallyConstant.const 0
  add_mem' := fun he hf => (he.prodMk hf).comp fun p => p.1 + p.2
  neg_mem' := fun he => he.comp Neg.neg

/-- The existing ordinary differential factored through ordinary cycles,
with its domain restricted to actual continuous two-cochains. -/
@[expose] def continuousBoundary3 : continuousTwo →+ cocycles GmRep 3 :=
  (toCocycles GmRep 2 3).hom.toAddMonoidHom.comp continuousTwo.subtype

/-- Quotient enough to test the class of a continuous cocycle. It is
intentionally not declared to be the whole continuous H³: ordinary
noncontinuous cycles are also present in its ambient numerator. -/
abbrev PrimitiveQuotient3 := cocycles GmRep 3 ⧸ continuousBoundary3.range

def erasedClass3 (z : cocycles GmRep 3) : PrimitiveQuotient3 :=
  QuotientAddGroup.mk z

theorem erased_eq_zero_iff (z : cocycles GmRep 3) :
    erasedClass3 z = 0 ↔ ∃ e : continuousTwo, continuousBoundary3 e = z := by
  exact QuotientAddGroup.eq_zero_iff z

/-- Exact scope of Milne ADT I.4.21 at Q (all places, r=3, T=G_m).
This is a proposition to supply from the arithmetic theorem, not
an axiom and not ordinary group cohomology vanishing. -/
@[expose] def MilneH3AtQ : Prop :=
  ∀ z : cocycles GmRep 3, IsLocallyConstant (iCocycles GmRep 3 z) → erasedClass3 z = 0

/-- A continuous cocycle of field units has a continuous primitive once
its erased class vanishes in the correctly restricted quotient. -/
theorem primitive_of_erased_zero (z : cocycles GmRep 3) (hz : erasedClass3 z = 0) :
    ∃ e : continuousTwo,
      inhomogeneousCochains.d GmRep 2 e.val = iCocycles GmRep 3 z := by
  obtain ⟨e, he⟩ := (erased_eq_zero_iff z).mp hz
  refine ⟨e, ?_⟩
  rw [← groupCohomology.inhomogeneousCochains.d_def GmRep 2,
    ← (groupCohomology.inhomogeneousCochains GmRep).toCycles_i 2 3]
  exact congrArg (iCocycles GmRep 3) he

/-- Forget the root-of-unity order bound, retaining the actual Galois
field-unit coefficient and the literal cochain values. -/
@[expose] def eraseRootBound (m : ℕ)
    (eta : (Fin 3 → GalQ) → rootsOfUnity m (AlgebraicClosure ℚ)) :
    (Fin 3 → GalQ) → GmRep :=
  fun g => Additive.ofMul (eta g).val

/-- Consumer for the finite-valued CT defect dσ ∪ τ'. The geometric cup
construction supplies its continuity and closedness. No local Brauer
invariant, local trace, or restricted sum appears in the conclusion. -/
theorem primitive_of_root_defect (hM : MilneH3AtQ) (m : ℕ)
    (eta : (Fin 3 → GalQ) → rootsOfUnity m (AlgebraicClosure ℚ))
    (hcont : IsLocallyConstant eta)
    (hclosed : inhomogeneousCochains.d GmRep 3 (eraseRootBound m eta) = 0) :
    ∃ e : continuousTwo,
      inhomogeneousCochains.d GmRep 2 e.val = eraseRootBound m eta := by
  let z := cocyclesMk (eraseRootBound m eta) hclosed
  have hz : iCocycles GmRep 3 z = eraseRootBound m eta :=
    iCocycles_mk _ _
  have hc : IsLocallyConstant (iCocycles GmRep 3 z) := by
    rw [hz]
    exact hcont.comp fun r => Additive.ofMul r.val
  obtain ⟨e, he⟩ := primitive_of_erased_zero z (hM z hc)
  exact ⟨e, he.trans hz⟩


/-- After restricting the same primitive, the raw local correction is
a 2-cocycle. Turning it into a Brauer class and evaluating a local
invariant are deliberately not part of this algebraic fact. -/
theorem corrected_local_is_cycle {C₂ C₃ : Type*} [AddCommGroup C₂] [AddCommGroup C₃]
    (d : C₂ →+ C₃) (raw e : C₂) (defect : C₃)
    (hRaw : d raw = defect) (hPrimitive : d e = defect) : d (raw - e) = 0 := by
  rw [map_sub, hRaw, hPrimitive, sub_self]

end CTFieldPrimitiveBoundary318
