module
public import CTActualGloballyFiniteIsogenySelmer318
public import OriginalCasselsTargetClassChord318
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Prod
public import Mathlib.LinearAlgebra.Pi
import all CTActualGloballyFiniteIsogenySelmer318
import all CTActualDualConnecting318
import all OriginalCasselsDyadicXClass318
import all CTGlobalSupportedSquareclassCode318
public section
noncomputable section

namespace CTActualFiniteIsogenyLinear318

open CTActualGloballyFiniteIsogenySelmer318 CTActualDualConnecting318
open CTActualQuadraticHOne318 CTGlobalSupportedSquareclassCode318
open CTGlobalSupportedLocalization318 ActualNaturalAllPlacesFinite318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentEllipticModel318
open OriginalCasselsDyadicXClass318 OriginalCasselsTargetClassChord318
open OriginalSelectedCasselsParity318

abbrev ScalarBits (K : Type) [Field K] := Additive (SquareClass K)

private theorem scalarClass_square_one {K : Type} [Field K] (x : SquareClass K) : x*x=1 := by
  refine QuotientGroup.induction_on x (fun u => ?_)
  let q := QuotientGroup.mk' (powMonoidHom (α:=Kˣ) 2).range
  change q u*q u=1
  calc
    q u*q u=q (u*u) := (map_mul q u u).symm
    _=1 := (QuotientGroup.eq_one_iff _).mpr ⟨u,pow_two u⟩

/-- The genuine squareclass group is naturally a ZMod 2 vector space. -/
instance scalarBitsModule (K : Type) [Field K] : Module (ZMod 2) (ScalarBits K) :=
  AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    exact scalarClass_square_one x.toMul)

section Field
variable (K : Type) [Field K] [CharZero K] [DecidableEq K]

def reverseClassHom (n : K) (hn : n≠0) : Point n →+ ScalarBits K where
  toFun P := Additive.ofMul (reverseValue K n hn P)
  map_zero' := rfl
  map_add' := by
    intro P Q
    change reverseValue K n hn (P+Q)=reverseValue K n hn P*reverseValue K n hn Q
    apply (scalarKummer K).injective
    apply Multiplicative.toAdd.injective
    rw [map_mul]
    exact map_add (connecting K n hn) P Q

def localPlane (e : Side) (n : K) (hn : n≠0) : Submodule (ZMod 2) (ScalarBits K) :=
  AddSubgroup.toZModSubmodule 2 (match e with
    | .forward => (xClassHom (actual_target_class_product n hn)).range
    | .reverse => (reverseClassHom K n hn).range)

theorem mem_localPlane {e : Side} (n : K) (hn : n≠0) (c : SquareClass K) :
    Additive.ofMul c ∈ localPlane K e n hn ↔ occurs e K n hn c := by
  cases e <;> rfl

end Field

def localize {K : Type} [Field K] [CharZero K] (f : ℚ →+* K) :
    ScalarBits ℚ →+ ScalarBits K where
  toFun z := Additive.ofMul (scalarMap ℚ f z.toMul)
  map_zero' := map_one (scalarMap ℚ f)
  map_add' x y := map_mul (scalarMap ℚ f) x.toMul y.toMul

local instance : DecidableEq ℝ := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _
local instance {n : ℕ} (i : Support n) : Fact i.val.Prime :=
  ⟨Nat.prime_of_mem_primeFactors i.property⟩

/-- Actual real and retained p-adic squareclass product. The prime
type is exactly primeFactors(6*n), not an abstract same-cardinality set. -/
abbrev RetainedSpace (n : ℕ) :=
  ScalarBits ℝ × ((i : Support n) → ScalarBits ℚ_[i.val])

def diagAdd (n : ℕ) : Code n →+ RetainedSpace n where
  toFun a :=
    (localize (algebraMap ℚ ℝ) (supportedCodeHom n a),
      fun i => localize (algebraMap ℚ ℚ_[i.val]) (supportedCodeHom n a))
  map_zero' := by
    apply Prod.ext
    · simp
    · funext i
      simp
  map_add' a b := by
    apply Prod.ext
    · simp
    · funext i
      simp

def diagonal (n : ℕ) : Code n →ₗ[ZMod 2] RetainedSpace n :=
  (diagAdd n).toZModLinearMap 2

theorem real_diag (n : ℕ) (a : Code n) :
    (diagonal n a).1 =
      Additive.ofMul (scalarMap ℚ (algebraMap ℚ ℝ) (supportedClass n a)) := rfl

theorem padic_diag (n : ℕ) (a : Code n) (i : Support n) :
    (diagonal n a).2 i =
      Additive.ofMul (scalarMap ℚ (algebraMap ℚ ℚ_[i.val]) (supportedClass n a)) := rfl

/-- The signed diagonal in actual local squareclasses is injective. -/
theorem diagonal_injective (n : ℕ) : Function.Injective (diagonal n) := by
  intro a b he
  apply actual_localization_jointly_injective n a b
  · have h := congrArg (fun z : RetainedSpace n => z.1.toMul) he
    rw [show (diagonal n a).1.toMul=scalarMap ℚ (algebraMap ℚ ℝ) (supportedClass n a) from rfl,
      show (diagonal n b).1.toMul=scalarMap ℚ (algebraMap ℚ ℝ) (supportedClass n b) from rfl] at h
    rw [supportedClass_value,supportedClass_value] at h
    exact ((scalarMap_on_unit ℚ (algebraMap ℚ ℝ) (Units.mk0 (scalar n a) (scalar_ne n a))).symm.trans
      (h.trans (scalarMap_on_unit ℚ (algebraMap ℚ ℝ) (Units.mk0 (scalar n b) (scalar_ne n b)))))
  · intro i
    dsimp only
    have h := congrArg (fun z : RetainedSpace n => (z.2 i).toMul) he
    rw [show ((diagonal n a).2 i).toMul=scalarMap ℚ (algebraMap ℚ ℚ_[i.val]) (supportedClass n a) from rfl,
      show ((diagonal n b).2 i).toMul=scalarMap ℚ (algebraMap ℚ ℚ_[i.val]) (supportedClass n b) from rfl] at h
    rw [supportedClass_value,supportedClass_value] at h
    exact ((scalarMap_on_unit ℚ (algebraMap ℚ ℚ_[i.val]) (Units.mk0 (scalar n a) (scalar_ne n a))).symm.trans
      (h.trans (scalarMap_on_unit ℚ (algebraMap ℚ ℚ_[i.val]) (Units.mk0 (scalar n b) (scalar_ne n b)))))

def globalDiagonal (n : ℕ) : Submodule (ZMod 2) (RetainedSpace n) :=
  (diagonal n).range

def realPlane (e : Side) (n : ℕ) (hn : 0<n) :=
  localPlane ℝ e (n:ℝ) (Nat.cast_ne_zero.mpr hn.ne')

def padicPlane (e : Side) (n : ℕ) (hn : 0<n) (i : Support n) :=
  localPlane ℚ_[i.val] e (n:ℚ_[i.val]) (Nat.cast_ne_zero.mpr hn.ne')

/-- Direct product of the genuinely occurring coordinate classes. -/
def localProduct (e : Side) (n : ℕ) (hn : 0<n) : Submodule (ZMod 2) (RetainedSpace n) where
  carrier := {z | z.1 ∈ realPlane e n hn ∧ ∀ i, z.2 i ∈ padicPlane e n hn i}
  zero_mem' := ⟨(realPlane e n hn).zero_mem,fun i => (padicPlane e n hn i).zero_mem⟩
  add_mem' hu hv := ⟨(realPlane e n hn).add_mem hu.1 hv.1,
    fun i => (padicPlane e n hn i).add_mem (hu.2 i) (hv.2 i)⟩
  smul_mem' t hu := ⟨(realPlane e n hn).smul_mem t hu.1,
    fun i => (padicPlane e n hn i).smul_mem t (hu.2 i)⟩

theorem diag_membership (e : Side) (n : ℕ) (hn : 0<n) (a : Code n) :
    diagonal n a ∈ localProduct e n hn ↔
      realCondition e n hn (supportedClass n a) ∧
      ∀ i : Support n, padicCondition e n hn i.val
        (Nat.prime_of_mem_primeFactors i.property) (supportedClass n a) := by
  change ((diagonal n a).1 ∈ realPlane e n hn ∧
            ∀ i, (diagonal n a).2 i ∈ padicPlane e n hn i) ↔ _
  simp only [real_diag,padic_diag,realPlane,padicPlane,mem_localPlane,realCondition,padicCondition]

def codeIntoIntersection (e : Side) (n : ℕ) (hn : 0<n) (a : retainedCode e n hn) :
    ↥(globalDiagonal n ⊓ localProduct e n hn) :=
  ⟨diagonal n a.val,⟨⟨a.val,rfl⟩,(diag_membership e n hn a.val).mpr a.property⟩⟩

/-- The true all-place scalar Selmer groups are the two literal
intersections W ∩ L in the same retained squareclass space. -/
def scalarSelmerIntersection (e : Side) (n : ℕ) (hn : 0<n) :
    scalarSelmer e n hn ≃ ↥(globalDiagonal n ⊓ localProduct e n hn) :=
  (actualScalarSelmerEquiv e n hn).symm.trans
    (Equiv.ofBijective (codeIntoIntersection e n hn) ⟨by
      intro a b h
      apply Subtype.ext
      apply diagonal_injective n
      exact congrArg Subtype.val h,by
      rintro ⟨z,hW,hL⟩
      obtain ⟨a,ha⟩ := hW
      have haL : diagonal n a ∈ localProduct e n hn := by
        rw [ha]
        exact hL
      exact ⟨⟨a,(diag_membership e n hn a).mp haL⟩,Subtype.ext ha⟩⟩)

end CTActualFiniteIsogenyLinear318

#print axioms CTActualFiniteIsogenyLinear318.scalarBitsModule
#print axioms CTActualFiniteIsogenyLinear318.diagonal_injective
#print axioms CTActualFiniteIsogenyLinear318.scalarSelmerIntersection
