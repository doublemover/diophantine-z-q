module
public import OriginalSelectedCasselsLocalArithmetic318
public import ActualTwoDescentEllipticModel318
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Real.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.LinearCombination
public section

noncomputable section

namespace OriginalSelectedCasselsParity318

open scoped BigOperators
open ActualTwoDescentEllipticModel318 OriginalSelectedCasselsLocalArithmetic318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : DecidableEq ℝ := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

section Local

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

/-- Literal quotient model for the genuine (0,0) 2-isogeny. -/
@[expose] def targetModel (n : F) : WeierstrassCurve F := ⟨0,-4*n,0,16*n^2,0⟩
abbrev TargetPoint (n : F) := (targetModel n).toAffine.Point

private theorem target_discriminant (n : F) :
    (targetModel n).Δ = -196608*n^6 := by
  simp only [WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈,targetModel]
  ring

private theorem target_equation (n x y : F) :
    (targetModel n).toAffine.Equation x y ↔ y^2=x*(x^2-4*n*x+16*n^2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [targetModel,zero_mul,add_zero,zero_add]
  constructor <;> intro h <;> linear_combination h

def targetPoint (n x y : F) (hn : n ≠ 0) (he : y^2=x*(x^2-4*n*x+16*n^2)) :
    TargetPoint n :=
  WeierstrassCurve.Affine.Point.some x y <|
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (show (targetModel n).Δ ≠ 0 by
        rw [target_discriminant]
        exact mul_ne_zero (by norm_num) (pow_ne_zero _ hn))).mp
      ((target_equation n x y).mpr he)

/-- This is the exact image formula on every nonzero source abscissa. -/
def imagePoint (n x y : F) (hn : n ≠ 0) (hx : x ≠ 0)
    (he : y^2=x*(x-n)*(x+3*n)) : TargetPoint n :=
  targetPoint n (x+2*n-3*n^2/x) (y+3*n^2*y/x^2) hn
    (affine_isogeny_chart n x y hx he)

/-- Arithmetic supplier: the actual additive homomorphism of local points
induced by the rational (0,0) isogeny. Its chart and finite true kernel
and range quotient are specified; no sign function is supplied here. -/
structure LocalIsogeny (n : F) (hn : n ≠ 0) where
  hom : Point n →+ TargetPoint n
  on_affine : ∀ (x y : F) (hx : x ≠ 0) (he : y^2=x*(x-n)*(x+3*n)),
    hom (point n x y hn he) = imagePoint n x y hn hx he
  at_kernel : hom (point n 0 0 hn (by simp)) = 0
  finiteKernel : Finite hom.ker
  finiteCokernel : Finite (TargetPoint n ⧸ hom.range)
  kernelCard : Nat.card hom.ker = 2

def LocalIsogeny.cokernelCard {n : F} {hn : n ≠ 0} (P : LocalIsogeny n hn) : ℕ :=
  Nat.card (TargetPoint n ⧸ P.hom.range)

/-- Read the sign of the *rational* cokernel/kernel ratio. Its signed
valuation can be −1 (cokernel size 1, kernel size 2). -/
@[expose] def ratioSign (c k : ℕ) : ℤ :=
  if padicValRat 2 ((c : ℚ)/(k : ℚ)) % 2 = 0 then 1 else -1

private theorem val_two : padicValRat 2 (2 : ℚ) = 1 := by
  change padicValRat 2 ((2 : ℕ) : ℚ) = 1
  rw [padicValRat.of_nat, padicValNat_self] <;> rfl

theorem ratio_sign_one_two : ratioSign 1 2 = -1 := by
  change (if padicValRat 2 ((1 : ℚ)/2) % 2 = 0 then (1:ℤ) else -1) = -1
  rw [padicValRat.div (by norm_num : (1:ℚ) ≠ 0) (by norm_num : (2:ℚ) ≠ 0),
    padicValRat.one, val_two] <;> decide

theorem ratio_sign_two_two : ratioSign 2 2 = 1 := by
  change (if padicValRat 2 ((2 : ℚ)/2) % 2 = 0 then (1:ℤ) else -1) = 1
  rw [div_self (show (2 : ℚ) ≠ 0 by norm_num), padicValRat.one] <;> decide

def LocalIsogeny.sign {n : F} {hn : n ≠ 0} (P : LocalIsogeny n hn) : ℤ :=
  ratioSign P.cokernelCard (Nat.card P.hom.ker)

theorem LocalIsogeny.sign_of_cokernel {n : F} {hn : n ≠ 0}
    (P : LocalIsogeny n hn) :
    (P.cokernelCard = 1 → P.sign = -1) ∧ (P.cokernelCard = 2 → P.sign = 1) := by
  constructor <;> intro h
  · rw [LocalIsogeny.sign,h,P.kernelCard,ratio_sign_one_two]
  · rw [LocalIsogeny.sign,h,P.kernelCard,ratio_sign_two_two]

end Local

/-- Exactly Q's archimedean place and one genuine completion at each prime. -/
structure LocalSystem (n : ℕ) (hn : 0 < n) where
  real : LocalIsogeny (n:ℝ) (Nat.cast_ne_zero.mpr hn.ne')
  padic : ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
    LocalIsogeny (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne')

def LocalSystem.finiteCokernelCard {n : ℕ} {hn : 0<n}
    (L : LocalSystem n hn) (p : ℕ) (hp : p.Prime) : ℕ := by
  letI : Fact p.Prime := ⟨hp⟩
  exact (L.padic p hp).cokernelCard

def LocalSystem.finiteSign {n : ℕ} {hn : 0<n} (L : LocalSystem n hn) (p : ℕ) : ℤ :=
  if hp : p.Prime then ratioSign (L.finiteCokernelCard p hp) 2 else 1

theorem LocalSystem.finiteSign_eq {n : ℕ} {hn : 0<n}
    (L : LocalSystem n hn) (p : ℕ) (hp : p.Prime) :
    L.finiteSign p = (letI : Fact p.Prime := ⟨hp⟩; (L.padic p hp).sign) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [LocalSystem.finiteSign,dif_pos hp]
  change ratioSign (L.padic p hp).cokernelCard 2 = (L.padic p hp).sign
  rw [LocalIsogeny.sign,(L.padic p hp).kernelCard]

/-- All actual local coker identifications from the direct paper calculation.
The good primes belong to this interface too: none may be silently omitted. -/
structure ExactLocalCokernels {n : ℕ} {hn : 0<n} (L : LocalSystem n hn) : Prop where
  real_size : L.real.cokernelCard = 1
  two_size : L.finiteCokernelCard 2 Nat.prime_two = 2
  three_size : L.finiteCokernelCard 3 Nat.prime_three = 1
  ramified_size : ∀ p ∈ n.primeFactors, ∀ hp : p.Prime,
    L.finiteCokernelCard p hp = if (p:ZMod 3) = 1 then 2 else 1
  good_size : ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 → p ≠ 3 → p ∉ n.primeFactors →
    L.finiteCokernelCard p hp = 2

end OriginalSelectedCasselsParity318
