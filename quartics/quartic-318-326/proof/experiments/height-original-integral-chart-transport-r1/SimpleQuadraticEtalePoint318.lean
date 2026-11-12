module
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Tactic
public section
noncomputable section
namespace SimpleQuadraticEtalePoint318
open Polynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (q : R)
@[expose] def equation : R[X] := X^2+(X-C q)
theorem monic : (equation q).Monic := by
  apply Polynomial.monic_X_pow_add
  calc
    degree (X-C q) ≤ max (degree (X : R[X])) (degree (C q)) := degree_sub_le _ _
    _ ≤ 1 := max_le degree_X_le (le_trans degree_C_le (by decide))
    _ < (2 : WithBot ℕ) := by decide
abbrev RootRing := AdjoinRoot (equation q)
@[expose] def derivativeValue : RootRing q := AdjoinRoot.mk (equation q) (equation q).derivative
abbrev EtaleRing := Localization.Away (derivativeValue q)
@[expose] def root : EtaleRing q :=
  algebraMap (RootRing q) (EtaleRing q) (AdjoinRoot.root (equation q))

theorem etale : Algebra.Etale R (EtaleRing q) := by
  let P : StandardEtalePair R :=
    { f := equation q
      monic_f := monic q
      g := (equation q).derivative
      cond := ⟨1,0,1,by simp⟩ }
  exact Algebra.Etale.of_equiv P.equivAwayAdjoinRoot

theorem root_equation : (root q)^2+root q=algebraMap R (EtaleRing q) q := by
  have h := AdjoinRoot.mk_self (f:=equation q)
  change AdjoinRoot.mk (equation q) (X^2+(X-C q))=0 at h
  rw [map_add,map_pow,AdjoinRoot.mk_X,map_sub,AdjoinRoot.mk_X,AdjoinRoot.mk_C] at h
  have hh := congrArg (algebraMap (RootRing q) (EtaleRing q)) h
  simp only [map_add,map_sub,map_pow,map_zero,←IsScalarTower.algebraMap_apply] at hh
  change (root q)^2+(root q-algebraMap R (EtaleRing q) q)=0 at hh
  linear_combination hh

variable {S : Type*} [CommRing S] (ev : R →+* S) (hq : ev q=0)
@[expose] def rootPoint : RootRing q →+* S :=
  AdjoinRoot.lift ev 0 (by
    simp only [equation,eval₂_add,eval₂_pow,eval₂_X,eval₂_sub,eval₂_C,hq,
      zero_pow (by decide : (2 : ℕ)≠0),sub_self,add_zero])
theorem rootPoint_polynomial (p : R[X]) :
    rootPoint q ev hq (AdjoinRoot.mk (equation q) p)=Polynomial.eval₂ ev 0 p :=
  AdjoinRoot.lift_mk _ _ _ p

theorem derivative_at_point : rootPoint q ev hq (derivativeValue q)=1 := by
  rw [derivativeValue,rootPoint_polynomial]
  simp [equation]

/-- The zero root is an ACTUAL point of the standard-etale derivative
open in every residue characteristic. Its derivative image is literally1,
so no inverse of2 is requested or smuggled into the integral base. -/
@[expose] def point : EtaleRing q →+* S :=
  IsLocalization.Away.lift (derivativeValue q)
    (by rw [derivative_at_point]; exact isUnit_one)

theorem point_on_root_ring (x : RootRing q) :
    point q ev hq (algebraMap (RootRing q) (EtaleRing q) x)=rootPoint q ev hq x :=
  IsLocalization.Away.lift_eq _ _ _
theorem point_root : point q ev hq (root q)=0 := by
  rw [root,point_on_root_ring]
  exact AdjoinRoot.lift_root _ _ _
theorem point_scalar (r : R) : point q ev hq (algebraMap R (EtaleRing q) r)=ev r := by
  rw [IsScalarTower.algebraMap_apply R (RootRing q) (EtaleRing q),point_on_root_ring]
  change rootPoint q ev hq (AdjoinRoot.mk (equation q) (C r))=ev r
  rw [rootPoint_polynomial,eval₂_C]
end SimpleQuadraticEtalePoint318
