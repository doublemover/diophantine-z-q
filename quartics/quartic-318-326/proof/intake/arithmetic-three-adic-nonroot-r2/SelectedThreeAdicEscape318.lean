module
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
namespace SelectedThreeAdicEscape318

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Homogeneous polynomials for the triple map, z=twist times x-denominator. -/
def D (a z : ℤ) : ℤ := 3*a^4+8*z*a^3-18*z^2*a^2-9*z^4
def N (a z : ℤ) : ℤ := a^9+36*z^2*a^7+48*z^3*a^6+270*z^4*a^5+
  864*z^5*a^4-396*z^6*a^3-1296*z^7*a^2+729*z^8*a
def H (a z : ℤ) : ℤ := a^12+8*z*a^11-66*z^2*a^10-1485*z^4*a^8-
  4752*z^5*a^7-5004*z^6*a^6+10080*z^7*a^5+2295*z^8*a^4-
  35640*z^9*a^3+16686*z^10*a^2+7776*z^11*a-2187*z^12

theorem triple_identity (a z : ℤ) :
    a*(a-z)*(a+3*z)*(H a z)^2 =
    N a z*(N a z-z*(D a z)^2)*(N a z+3*z*(D a z)^2) := by
  unfold N H D
  ring

def C (a v : ℤ) : ℤ := a^4+24*v*a^3-486*v^2*a^2-19683*v^4
theorem D_factor (a v : ℤ) : D a (9*v)=3*C a v := by unfold D C; ring

theorem residues (a v : ℤ) :
    ((N a (9*v) : ℤ) : ZMod 3)=(a:ZMod 3)^9 ∧
    ((C a v : ℤ) : ZMod 3)=(a:ZMod 3)^4 := by
  unfold N C
  push_cast
  generalize (a : ZMod 3) = A
  generalize (v : ZMod 3) = V
  revert A V
  decide +kernel

/-- Exact rational point with x=a/(9b), a a 3-adic unit. No group law,
formal group, Selmer cardinality, or assumed supply of new points. -/
structure Seed (n : ℤ) where
  a : ℤ
  b : ℤ
  y : ℚ
  unitA : (a : ZMod 3) ≠ 0
  nzB : b ≠ 0
  eqn : ((9*b:ℤ):ℚ)^3 * y^2 = (a*(a-9*(n*b))*(a+3*(9*(n*b))) : ℤ)

private theorem nz_of_unit {a : ℤ} (h : (a : ZMod 3) ≠ 0) : a ≠ 0 := by
  intro he
  simp [he] at h

private theorem val_unit {a : ℤ} (h : (a : ZMod 3) ≠ 0) :
    padicValRat 3 (a:ℚ)=0 := by
  have hu : ¬(3 : ℤ) ∣ a := fun he => h ((ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mpr he)
  simp only [padicValRat.of_int,padicValInt.eq_zero_of_not_dvd hu,Nat.cast_zero]

theorem Seed.d_ne {n : ℤ} (s : Seed n) : D s.a (9*(n*s.b)) ≠ 0 := by
  rw [D_factor]
  exact mul_ne_zero (by decide) (nz_of_unit (by
    rw [(residues s.a (n*s.b)).2]; exact pow_ne_zero _ s.unitA))

def step {n : ℤ} (s : Seed n) : Seed n where
  a := N s.a (9*(n*s.b))
  b := s.b*(D s.a (9*(n*s.b)))^2
  y := s.y*(H s.a (9*(n*s.b)):ℚ)/(D s.a (9*(n*s.b)):ℚ)^3
  unitA := by rw [(residues _ _).1]; exact pow_ne_zero _ s.unitA
  nzB := mul_ne_zero s.nzB (pow_ne_zero _ s.d_ne)
  eqn := by
    let z := 9*(n*s.b)
    let d := D s.a z
    let h := H s.a z
    let u := N s.a z
    have hd : (d:ℚ) ≠ 0 := Int.cast_ne_zero.mpr s.d_ne
    have he := s.eqn
    have hi := congrArg (fun t : ℤ => (t : ℚ)) (triple_identity s.a z)
    change _ = ((u*(u-9*(n*(s.b*d^2)))*(u+3*(9*(n*(s.b*d^2)))) : ℤ):ℚ)
    change ((9*(s.b*d^2):ℤ):ℚ)^3 * (s.y*(h:ℚ)/(d:ℚ)^3)^2 = _
    change ((9*s.b:ℤ):ℚ)^3*s.y^2 = ((s.a*(s.a-z)*(s.a+3*z):ℤ):ℚ) at he
    change ((s.a*(s.a-z)*(s.a+3*z)*h^2:ℤ):ℚ) =
      ((u*(u-z*d^2)*(u+3*z*d^2):ℤ):ℚ) at hi
    push_cast at he hi ⊢
    have hz : (z:ℚ) = 9*((n:ℚ)*(s.b:ℚ)) := by simp [z]
    calc
      _ = (9*(s.b:ℚ))^3*s.y^2*(h:ℚ)^2 := by field_simp; ring
      _ = _ := by rw [he, hi, hz]; ring

def Seed.x {n : ℤ} (s : Seed n) : ℚ := s.a/(9*(s.b:ℚ))

theorem Seed.onCurve {n : ℤ} (s : Seed n) :
    s.y^2=s.x*(s.x-n)*(s.x+3*n) := by
  have h := s.eqn
  push_cast at h
  have hb : (s.b:ℚ) ≠ 0 := Int.cast_ne_zero.mpr s.nzB
  have hd : (9:ℚ)*(s.b:ℚ) ≠ 0 := mul_ne_zero (by norm_num) hb
  apply (mul_left_cancel₀ (pow_ne_zero 3 hd))
  calc
    _ = (s.a:ℚ)*(s.a-9*((n:ℚ)*s.b))*(s.a+3*(9*((n:ℚ)*s.b))) := h
    _ = _ := by unfold Seed.x; field_simp; ring

theorem val_step {n : ℤ} (s : Seed n) :
    padicValRat 3 (step s).x = padicValRat 3 s.x - 2 := by
  let v := n*s.b
  let d := D s.a (9*v)
  have hd : (d:ℚ) ≠ 0 := Int.cast_ne_zero.mpr s.d_ne
  have hc : ((C s.a v:ℤ):ZMod 3) ≠ 0 := by
    rw [(residues _ _).2]; exact pow_ne_zero _ s.unitA
  have h3 : padicValRat 3 (3:ℚ) = 1 := padicValRat.self (by decide : 1 < 3)
  have hdv : padicValRat 3 (d:ℚ)=1 := by
    have hcQ : (C s.a v : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (nz_of_unit hc)
    change padicValRat 3 ((D s.a (9*v):ℤ):ℚ)=1
    rw [D_factor,Int.cast_mul,Int.cast_ofNat,padicValRat.mul (p := 3) (by decide : (3:ℚ)≠0) hcQ,
      h3,val_unit hc,add_zero]
  have hb : (s.b:ℚ) ≠ 0 := Int.cast_ne_zero.mpr s.nzB
  have hden : (9:ℚ)*(s.b:ℚ) ≠ 0 := mul_ne_zero (by norm_num) hb
  have hden' : (9:ℚ)*((step s).b:ℚ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr (step s).nzB)
  unfold Seed.x
  rw [padicValRat.div (Int.cast_ne_zero.mpr (nz_of_unit (step s).unitA)) hden',
    padicValRat.div (Int.cast_ne_zero.mpr (nz_of_unit s.unitA)) hden,
    val_unit (step s).unitA,val_unit s.unitA]
  have hbb : (9:ℚ)*((step s).b:ℚ) = (9*(s.b:ℚ))*(d:ℚ)^2 := by
    change 9*((s.b*d^2:ℤ):ℚ)=_; push_cast; ring
  rw [hbb,padicValRat.mul hden (pow_ne_zero _ hd),padicValRat.pow,hdv]
  norm_num

def iter {n : ℤ} (s : Seed n) : ℕ → Seed n
  | 0 => s
  | k+1 => step (iter s k)

theorem iter_val {n : ℤ} (s : Seed n) (k : ℕ) :
    padicValRat 3 (iter s k).x = padicValRat 3 s.x - 2*(k:ℤ) := by
  induction k with
  | zero => simp [iter]
  | succ k ih => rw [iter,val_step,ih,Nat.cast_succ]; ring

theorem iter_x_injective {n : ℤ} (s : Seed n) :
    Function.Injective (fun k => (iter s k).x) := by
  intro i j he
  have h := congrArg (padicValRat 3) he
  change padicValRat 3 (iter s i).x=padicValRat 3 (iter s j).x at h
  rw [iter_val,iter_val] at h
  omega

end SelectedThreeAdicEscape318
