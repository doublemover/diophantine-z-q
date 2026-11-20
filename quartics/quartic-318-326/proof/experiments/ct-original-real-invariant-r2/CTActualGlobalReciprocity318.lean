module
public import CTLocalInvariantDescent318
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import all CTLocalInvariantDescent318
import all CTContinuousFieldHTwo318
import all CTFieldPrimitiveRestriction318
import all CTFieldPrimitiveBoundary318
import Mathlib.Tactic.Abel
public section
noncomputable section

namespace CTActualGlobalReciprocity318

open scoped BigOperators
open CategoryTheory groupCohomology
open CTFieldPrimitiveRestriction318 CTContinuousFieldHTwo318 CTLocalInvariantDescent318

abbrev PrimePlace := {p : ℕ // p.Prime}
/-- The real place is none, and every rational prime occurs once. -/
abbrev Place := Option PrimePlace

local instance (p : PrimePlace) : Fact p.val.Prime := ⟨p.property⟩
local instance (p : PrimePlace) : DecidableEq (ℚ_[p.val]) := Classical.decEq _
local instance : DecidableEq ℝ := Classical.decEq _

/-- Literal completions, not placeholders. The theorem below does
not construct these canonical arithmetic homomorphisms. -/
structure LocalInvariants where
  real : ContH2 ℝ →+ InvValues
  finite : ∀ p : PrimePlace, ContH2 (ℚ_[p.val]) →+ InvValues

abbrev LocalCycles :=
  continuousCycles ℝ × ((p : PrimePlace) → continuousCycles (ℚ_[p.val]))

abbrev LocalRaw :=
  ((Fin 2 → Gal ℝ) → FieldUnitRep ℝ) ×
    ((p : PrimePlace) → (Fin 2 → Gal (ℚ_[p.val])) → FieldUnitRep (ℚ_[p.val]))

def localProfile (I : LocalInvariants) (z : LocalCycles) : Place → InvValues
  | none => I.real (classOf ℝ z.1)
  | some p => I.finite p (classOf (ℚ_[p.val]) (z.2 p))

/-- Restriction of an actual global continuous field-unit class to
the actual local class group, followed by the supplied invariant. -/
def globalProfile (I : LocalInvariants) (b : ContH2 ℚ) : Place → InvValues
  | none => I.real (restrictClass (algebraMap ℚ ℝ) b)
  | some p => I.finite p (restrictClass (algebraMap ℚ (ℚ_[p.val])) b)

def SupportedOn (u : Place → InvValues) (S : Finset Place) : Prop :=
  ∀ v, v ∉ S → u v=0

def FiniteProfile (u : Place → InvValues) : Prop :=
  ∃ S : Finset Place, SupportedOn u S

/-- Exactly the support-and-zero-sum half of Albert–Brauer–Hasse–Noether,
transported to the native continuous cohomology and literal places.
No injectivity/surjectivity clause or support of a corrected cup
is demanded as part of this arithmetic input. -/
def BrauerReciprocity (I : LocalInvariants) : Prop :=
  ∀ b : ContH2 ℚ, ∃ S : Finset Place, SupportedOn (globalProfile I b) S ∧
    (∑ v ∈ S, globalProfile I b v)=0

theorem sum_agrees_on_supports (u : Place → InvValues) (S T : Finset Place)
    (hS : SupportedOn u S) (hT : SupportedOn u T) :
    (∑ v ∈ S, u v) = ∑ v ∈ T, u v := by
  have hs : (∑ v ∈ S, u v) = ∑ v ∈ S ∪ T, u v :=
    Finset.sum_subset (fun _ h => Finset.mem_union_left _ h) (fun v _ h => hS v h)
  have ht : (∑ v ∈ T, u v) = ∑ v ∈ S ∪ T, u v :=
    Finset.sum_subset (fun _ h => Finset.mem_union_right _ h) (fun v _ h => hT v h)
  exact hs.trans ht.symm

/-- An ordinary finite sum, with no topological summation and no
arbitrary choice of a support affecting its value. -/
def finiteTotal (u : Place → InvValues) (h : FiniteProfile u) : InvValues :=
  ∑ v ∈ Classical.choose h, u v

theorem finiteTotal_on (u : Place → InvValues) (h : FiniteProfile u)
    (S : Finset Place) (hS : SupportedOn u S) :
    finiteTotal u h = ∑ v ∈ S, u v :=
  sum_agrees_on_supports u (Classical.choose h) S (Classical.choose_spec h) hS

/-- The original finite-sum ledger: supports of the first corrected
profile and of a global restriction imply support of its shifted
profile. No separate support hypothesis on the shifted profile. -/
theorem subtract_zero_sum (u b u' : Place → InvValues) (S T : Finset Place)
    (hS : SupportedOn u S) (hT : SupportedOn b T) (hb : (∑ v ∈ T, b v)=0)
    (he : ∀ v, u' v = u v-b v) :
    SupportedOn u' (S ∪ T) ∧ (∑ v ∈ S ∪ T, u' v) = ∑ v ∈ S, u v := by
  have suppS : SupportedOn u (S ∪ T) := by
    intro v hv
    exact hS v (fun h => hv (Finset.mem_union_left _ h))
  have suppT : SupportedOn b (S ∪ T) := by
    intro v hv
    exact hT v (fun h => hv (Finset.mem_union_right _ h))
  refine ⟨?_,?_⟩
  · intro v hv
    rw [he,suppS v hv,suppT v hv,sub_zero]
  · calc
      _ = ∑ v ∈ S ∪ T, (u v-b v) := Finset.sum_congr rfl (fun v _ => he v)
      _ = (∑ v ∈ S ∪ T, u v)-(∑ v ∈ S ∪ T, b v) := Finset.sum_sub_distrib
      _ = _ := by
        rw [sum_agrees_on_supports b (S ∪ T) T suppT hT,hb,sub_zero,
          sum_agrees_on_supports u (S ∪ T) S suppS hS]

/-- One and the same global 2-cycle is subtracted at every actual
place. Using separate local choices would not invoke reciprocity. -/
def GlobalCycleShift (b : continuousCycles ℚ) (z z' : LocalCycles) : Prop :=
  z'.1.val = z.1.val - restrictCochain (algebraMap ℚ ℝ) 2 b.val ∧
  ∀ p : PrimePlace,
    (z'.2 p).val = (z.2 p).val -
      restrictCochain (algebraMap ℚ (ℚ_[p.val])) 2 b.val

theorem local_profile_shift (I : LocalInvariants) (b : continuousCycles ℚ)
    (z z' : LocalCycles) (h : GlobalCycleShift b z z') (v : Place) :
    localProfile I z' v = localProfile I z v - globalProfile I (classOf ℚ b) v := by
  cases v with
  | none =>
    change I.real (classOf ℝ z'.1) =
      I.real (classOf ℝ z.1) - I.real (restrictClass (algebraMap ℚ ℝ) (classOf ℚ b))
    rw [subtract_global_cycle_class (algebraMap ℚ ℝ) b z.1 z'.1 h.1,map_sub]
  | some p =>
    change I.finite p (classOf (ℚ_[p.val]) (z'.2 p)) =
      I.finite p (classOf (ℚ_[p.val]) (z.2 p)) -
        I.finite p (restrictClass (algebraMap ℚ (ℚ_[p.val])) (classOf ℚ b))
    rw [subtract_global_cycle_class (algebraMap ℚ (ℚ_[p.val])) b (z.2 p) (z'.2 p) (h.2 p),
      map_sub]

theorem total_of_global_shift (I : LocalInvariants) (hR : BrauerReciprocity I)
    (b : continuousCycles ℚ) (z z' : LocalCycles) (h : GlobalCycleShift b z z')
    (hFin : FiniteProfile (localProfile I z)) :
    ∃ h' : FiniteProfile (localProfile I z'),
      finiteTotal (localProfile I z') h' = finiteTotal (localProfile I z) hFin := by
  let S := Classical.choose hFin
  have hS : SupportedOn (localProfile I z) S := Classical.choose_spec hFin
  obtain ⟨T,hT,hb⟩ := hR (classOf ℚ b)
  obtain ⟨hU,hEq⟩ := subtract_zero_sum (localProfile I z) (globalProfile I (classOf ℚ b))
    (localProfile I z') S T hS hT hb (local_profile_shift I b z z' h)
  let h' : FiniteProfile (localProfile I z') := ⟨S ∪ T,hU⟩
  exact ⟨h', (finiteTotal_on _ h' (S ∪ T) hU).trans
    (hEq.trans (finiteTotal_on _ hFin S hS).symm)⟩

def CorrectedFromRaw (raw : LocalRaw) (e : CTFieldPrimitiveBoundary318.continuousTwo)
    (z : LocalCycles) : Prop :=
  z.1.val = raw.1 - restrictCochain (algebraMap ℚ ℝ) 2 e.val ∧
  ∀ p : PrimePlace,
    (z.2 p).val = raw.2 p - restrictCochain (algebraMap ℚ (ℚ_[p.val])) 2 e.val

/-- The difference e'−e of two actual global primitives of the same
defect is one global locally constant 2-cycle. -/
def differenceCycle (e e' : CTFieldPrimitiveBoundary318.continuousTwo)
    (h : inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e'.val =
      inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e.val) :
    continuousCycles ℚ :=
  ⟨e'.val-e.val,⟨by rw [map_sub,h,sub_self],(e'.property.prodMk e.property).comp (fun p => p.1-p.2)⟩⟩

private theorem shift_cochain (L : Type) [Field L] [CharZero L] (f : ℚ →+* L)
    (r : (Fin 2 → Gal L) → FieldUnitRep L) (e e' : CTFieldPrimitiveBoundary318.continuousTwo) :
    r-restrictCochain f 2 e'.val =
      (r-restrictCochain f 2 e.val)-restrictCochain f 2 (e'.val-e.val) := by
  change _ = (r-restrictCochain f 2 e.val)-((unitRestrictionComplex f).f 2) (e'.val-e.val)
  rw [map_sub]
  change r-restrictCochain f 2 e'.val =
    r-restrictCochain f 2 e.val-(restrictCochain f 2 e'.val-restrictCochain f 2 e.val)
  abel

/-- Primitive-choice independence of the total for the SAME raw local
cups (hence the same recorded local corrections), under the honest
arithmetic reciprocity input. The representative changes locally. -/
theorem corrected_total_primitive_independent (I : LocalInvariants) (hR : BrauerReciprocity I)
    (raw : LocalRaw) (e e' : CTFieldPrimitiveBoundary318.continuousTwo)
    (hPrim : inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e'.val =
      inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e.val)
    (z z' : LocalCycles) (hz : CorrectedFromRaw raw e z) (hz' : CorrectedFromRaw raw e' z')
    (hFin : FiniteProfile (localProfile I z)) :
    ∃ h' : FiniteProfile (localProfile I z'),
      finiteTotal (localProfile I z') h' = finiteTotal (localProfile I z) hFin := by
  let b := differenceCycle e e' hPrim
  apply total_of_global_shift I hR b z z' _ hFin
  constructor
  · rw [hz.1,hz'.1]
    exact shift_cochain ℝ (algebraMap ℚ ℝ) raw.1 e e'
  · intro p
    rw [hz.2 p,hz'.2 p]
    exact shift_cochain (ℚ_[p.val]) (algebraMap ℚ (ℚ_[p.val])) (raw.2 p) e e'

/-- A different global primitive can use the very same raw local
cups. Construct the new actual continuous cycles by subtracting
the restrictions of e'−e; no replacement local point is chosen. -/
theorem corrected_total_change_primitive (I : LocalInvariants) (hR : BrauerReciprocity I)
    (raw : LocalRaw) (e e' : CTFieldPrimitiveBoundary318.continuousTwo)
    (hPrim : inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e'.val =
      inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e.val)
    (z : LocalCycles) (hz : CorrectedFromRaw raw e z)
    (hFin : FiniteProfile (localProfile I z)) :
    ∃ z' : LocalCycles, CorrectedFromRaw raw e' z' ∧
      ∃ h' : FiniteProfile (localProfile I z'),
        finiteTotal (localProfile I z') h' = finiteTotal (localProfile I z) hFin := by
  let b := differenceCycle e e' hPrim
  let z' : LocalCycles :=
    ⟨z.1 - restrictCycles (algebraMap ℚ ℝ) b,
      fun p => z.2 p - restrictCycles (algebraMap ℚ (ℚ_[p.val])) b⟩
  have hz' : CorrectedFromRaw raw e' z' := by
    constructor
    · change z.1.val - restrictCochain (algebraMap ℚ ℝ) 2 (e'.val-e.val) = _
      rw [hz.1]
      exact (shift_cochain ℝ (algebraMap ℚ ℝ) raw.1 e e').symm
    · intro p
      change (z.2 p).val - restrictCochain (algebraMap ℚ (ℚ_[p.val])) 2 (e'.val-e.val) = _
      rw [hz.2 p]
      exact (shift_cochain (ℚ_[p.val]) (algebraMap ℚ (ℚ_[p.val])) (raw.2 p) e e').symm
  exact ⟨z',hz',corrected_total_primitive_independent I hR raw e e' hPrim z z' hz hz' hFin⟩

end CTActualGlobalReciprocity318
