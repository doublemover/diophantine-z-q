module
public import CTContinuousFieldHTwo318
public import Mathlib.Topology.Instances.AddCircle.Defs
import all CTContinuousFieldHTwo318
import all CTFieldPrimitiveRestriction318
public section
noncomputable section

namespace CTLocalInvariantDescent318

open CategoryTheory groupCohomology CTFieldPrimitiveRestriction318 CTContinuousFieldHTwo318

variable {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L]
  [DecidableEq K] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _

/-- Literal cochain restriction on continuous one-cochains. -/
def restrictOne (f : K →+* L) : continuousOne K →+ continuousOne L where
  toFun u := ⟨restrictCochain f 1 u.val,restrict_locallyConstant f 1 u.val u.property⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero ((unitRestrictionComplex f).f 1)
  map_add' u v := by
    apply Subtype.ext
    exact map_add ((unitRestrictionComplex f).f 1) u.val v.val

/-- Restriction on the actual continuous cycles, retaining the native
chain map and hence the same closure embedding. -/
def restrictCycles (f : K →+* L) : continuousCycles K →+ continuousCycles L where
  toFun z := ⟨restrictCochain f 2 z.val,by
    have hz : inhomogeneousCochains.d (FieldUnitRep K) 2 z.val=0 := z.property.1
    have hc : IsLocallyConstant z.val := z.property.2
    refine ⟨?_,restrict_locallyConstant f 2 z.val hc⟩
    rw [restrict_d,hz] <;> exact map_zero ((unitRestrictionComplex f).f 3)⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero ((unitRestrictionComplex f).f 2)
  map_add' u v := by
    apply Subtype.ext
    exact map_add ((unitRestrictionComplex f).f 2) u.val v.val

theorem restriction_of_boundary (f : K →+* L) (u : continuousOne K) :
    restrictCycles f (continuousBoundary K u) =
      continuousBoundary L (restrictOne f u) := by
  apply Subtype.ext
  exact (restrict_d f 1 u.val).symm

/-- Actual continuous class restriction. This is not a Brauer-group
isomorphism, nor a local invariant map. -/
def restrictClass (f : K →+* L) : ContH2 K →+ ContH2 L :=
  QuotientAddGroup.lift _ ((classOf L).comp (restrictCycles f)) (by
    rintro _ ⟨u,rfl⟩
    change classOf L (restrictCycles f (continuousBoundary K u))=0
    rw [restriction_of_boundary]
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨restrictOne f u,rfl⟩)

@[simp] theorem restrict_class_of (f : K →+* L) (z : continuousCycles K) :
    restrictClass f (classOf K z) = classOf L (restrictCycles f z) :=
  QuotientAddGroup.lift_mk' _ _ z

/-- A global primitive change by a continuous 2-cycle changes the
local class by NEGATIVE restriction, not in general by a local
boundary. Arithmetic reciprocity is what would kill its place sum. -/
theorem subtract_global_cycle_class (f : K →+* L) (b : continuousCycles K)
    (z z' : continuousCycles L)
    (h : z'.val = z.val - restrictCochain f 2 b.val) :
    classOf L z' = classOf L z - restrictClass f (classOf K b) := by
  have h' : z'=z-restrictCycles f b := Subtype.ext h
  rw [h',map_sub,restrict_class_of]

abbrev InvValues := AddCircle (1 : ℚ)

/-- The exact descent required of an externally supplied arithmetic
evaluation defined on cycles. A homomorphism with this property is
not asserted to be the canonical local invariant. -/
def descendInvariant (v : continuousCycles L →+ InvValues)
    (h : ∀ u : continuousOne L, v (continuousBoundary L u)=0) :
    ContH2 L →+ InvValues :=
  QuotientAddGroup.lift _ v (by rintro _ ⟨u,rfl⟩; exact h u)

@[simp] theorem descend_invariant_class (v : continuousCycles L →+ InvValues)
    (h : ∀ u : continuousOne L, v (continuousBoundary L u)=0)
    (z : continuousCycles L) :
    descendInvariant v h (classOf L z)=v z :=
  QuotientAddGroup.lift_mk' _ _ z

/-- Independence of the numerical value under an actual continuous
one-cochain boundary, for any supplied invariant of the class group. -/
theorem invariant_eq_of_boundary (v : ContH2 L →+ InvValues)
    (z z' : continuousCycles L) (u : continuousOne L)
    (h : z.val-z'.val = inhomogeneousCochains.d (FieldUnitRep L) 1 u.val) :
    v (classOf L z)=v (classOf L z') :=
  congrArg v (class_eq_of_boundary L z z' u h)

end CTLocalInvariantDescent318
