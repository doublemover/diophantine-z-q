module
public import CTLiteralDualComposite318
public import OriginalCasselsLiteralIsogenyAddition318
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import all OriginalSelectedCasselsParity318
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
public section
noncomputable section

namespace CTLiteralDualGeometricHom318

open CTLiteralDualComposite318 CTLiteralDualFiberTargetPoints318
open OriginalCasselsLiteralIsogenyPoint318 OriginalCasselsLiteralIsogenyAddition318
open ActualTwoDescentEllipticModel318 OriginalSelectedCasselsParity318

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]

/-- Geometric surjectivity of the actual forward point map, with
the literal (n,0) above (0,0), not a square root of zero. -/
theorem literal_geometric_surjective (n : K) (hn : n≠0) :
    Function.Surjective (literalMap n hn) := by
  intro Q
  cases Q with
  | zero => exact ⟨0,literal_zero n hn⟩
  | some s t w =>
    have he := w.left
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simp only [targetModel,zero_mul,add_zero,zero_add] at he
    have hT : t^2=s*(s^2-4*n*s+16*n^2) := by linear_combination he
    change ∃ P, literalMap n hn P=targetPoint n s t hn hT
    by_cases hs : s=0
    · subst s
      have ht : t=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa using hT)
      subst t
      exact ⟨point n n 0 hn (by simp),literal_target_kernel_fiber n hn⟩
    obtain ⟨r,hr⟩ := IsAlgClosed.exists_pow_nat_eq s (by decide : 0<(2:ℕ))
    exact literal_affine_fiber n s t r hn hs hr hT

/-- Reverse additivity is deduced from genuine forward additivity
and the verified [2] composition, via the actual geometric fibers. -/
theorem dual_geometric_add (n : K) (hn : n≠0) (P Q : TargetPoint n) :
    dualPoint n hn (P+Q)=dualPoint n hn P+dualPoint n hn Q := by
  obtain ⟨p,rfl⟩ := literal_geometric_surjective n hn P
  obtain ⟨q,rfl⟩ := literal_geometric_surjective n hn Q
  rw [←literal_addition n hn p q,dual_literal_add_self,dual_literal_add_self,dual_literal_add_self]
  abel

def geometricDualHom (n : K) (hn : n≠0) : TargetPoint n →+ Point n where
  toFun := dualPoint n hn
  map_zero' := dual_zero n hn
  map_add' := dual_geometric_add n hn

theorem literal_dual_add_self (n : K) (hn : n≠0) (Q : TargetPoint n) :
    literalMap n hn (dualPoint n hn Q)=Q+Q := by
  obtain ⟨p,rfl⟩ := literal_geometric_surjective n hn Q
  rw [dual_literal_add_self,literal_addition n hn p p]

end CTLiteralDualGeometricHom318

#print axioms CTLiteralDualGeometricHom318.literal_geometric_surjective
#print axioms CTLiteralDualGeometricHom318.geometricDualHom
#print axioms CTLiteralDualGeometricHom318.literal_dual_add_self
