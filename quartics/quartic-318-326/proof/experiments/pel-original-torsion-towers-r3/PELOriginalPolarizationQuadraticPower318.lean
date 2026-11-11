module
public import PELOriginalNormalizedRelativePolarization318
public import PELOriginalAlgebraicLineSymmetry318
public import PELOriginalIntegerMultiplication318
public import Mathlib.Algebra.Group.Basic
public section
noncomputable section
namespace PELOriginalPolarizationQuadraticPower318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalSchemePointGroup318 PELOriginalCubeTestClasses318
open PELOriginalPolarizationBicharacter318 PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im) {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))

/-- The genuine zero-normalized line class. Its quadratic law keeps
track of the original zero-map line rather than silently trivializing it. -/
@[expose] def q (a : Points τ hτ Y ρ) : Class Y :=
  value τ hτ ρ a*(value τ hτ ρ 0)⁻¹
lemma q_zero : q τ hτ ρ 0=1 := by simp only [q,mul_inv_cancel]
lemma value_neg (a : Points τ hτ Y ρ) : value τ hτ ρ (-a)=value τ hτ ρ a := by
  have h := congrArg (LineClassPullbackHom318.pullback a.val)
    (PELOriginalAlgebraicLineSymmetry318.class_invariant τ hτ)
  rw [class_composition] at h
  exact h
lemma q_neg (a : Points τ hτ Y ρ) : q τ hτ ρ (-a)=q τ hτ ρ a := by
  rw [q,q,value_neg]
lemma q_add (a b : Points τ hτ Y ρ) :
    q τ hτ ρ (a+b)=pairing τ hτ ρ a b*q τ hτ ρ a*q τ hτ ρ b := by
  simp only [q,pairing]
  group
lemma diagonal (a : Points τ hτ Y ρ) : pairing τ hτ ρ a a=(q τ hτ ρ a)^2 := by
  have h : pairing τ hτ ρ a a*pairing τ hτ ρ a (-a)=1 := by
    rw [←add_right,add_neg_cancel,zero_right]
  have hn : pairing τ hτ ρ a (-a)=((q τ hτ ρ a)^2)⁻¹ := by
    simp only [pairing,add_neg_cancel,value_neg,q]
    group
  rw [hn] at h
  calc
    _ = (pairing τ hτ ρ a a*((q τ hτ ρ a)^2)⁻¹)*(q τ hτ ρ a)^2 := by group
    _ = _ := by rw [h,one_mul]
lemma pairing_nsmul_left (a b : Points τ hτ Y ρ) (n : ℕ) :
    pairing τ hτ ρ (n • a) b=(pairing τ hτ ρ a b)^n := by
  induction n with
  | zero => simp only [zero_nsmul,zero_left,pow_zero]
  | succ n ih => rw [succ_nsmul,add_left,ih,pow_succ]
lemma q_nsmul (a : Points τ hτ Y ρ) (n : ℕ) :
    q τ hτ ρ (n • a)=(q τ hτ ρ a)^(n*n) := by
  induction n with
  | zero => simp only [zero_nsmul,q_zero,Nat.zero_mul,pow_zero]
  | succ n ih =>
    rw [succ_nsmul,q_add,pairing_nsmul_left,diagonal,ih,←pow_mul,←pow_add,←pow_succ]
    congr 1
    ring

/-- Integer-square law at EVERY scheme-valued point, derived from the
actual universal cube and the actual algebraic negation isomorphism. -/
theorem q_zsmul (a : Points τ hτ Y ρ) (n : ℤ) :
    q τ hτ ρ (n • a)=(q τ hτ ρ a)^(n.natAbs*n.natAbs) := by
  cases n with
  | ofNat n =>
    change q τ hτ ρ ((n : ℤ) • a)=(q τ hτ ρ a)^(n*n)
    rw [natCast_zsmul]
    exact q_nsmul τ hτ ρ a n
  | negSucc n =>
    rw [negSucc_zsmul,q_neg]
    exact q_nsmul τ hτ ρ a (n+1)
end PELOriginalPolarizationQuadraticPower318
