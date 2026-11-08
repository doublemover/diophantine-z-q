module
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Tactic
public section
noncomputable section
namespace MonicRootEtale318
open Polynomial
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R] (p:R[X]) (hp:p.Monic)

theorem derivative_unit (hs:p.Separable) :
    IsUnit (AdjoinRoot.mk p p.derivative) := by
  obtain ⟨a,b,h⟩:=hs
  have hm:=congrArg (AdjoinRoot.mk p) h
  simp only [map_add,map_mul,AdjoinRoot.mk_self,map_one,mul_zero,zero_add] at hm
  exact IsUnit.of_mul_eq_one_right _ hm

@[expose] def pair : StandardEtalePair R where
  f:=p
  monic_f:=hp
  g:=p.derivative
  cond:=⟨1,0,1,by simp⟩

@[expose] def standardEquiv (hs:p.Separable) :
    (pair p hp).Ring ≃ₐ[R] AdjoinRoot p :=
  (pair p hp).equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (AdjoinRoot p)
      (Localization.Away (AdjoinRoot.mk p p.derivative))
      _ (derivative_unit p hs)).symm.restrictScalars R)

include hp in
theorem root_etale (hs:p.Separable) : Algebra.Etale R (AdjoinRoot p) :=
  Algebra.Etale.of_equiv (standardEquiv p hp hs)

include hp in
theorem root_faithfullyFlat [Nontrivial R] (hn:0<p.natDegree) :
    Module.FaithfullyFlat R (AdjoinRoot p) := by
  let : Module.Free R (AdjoinRoot p):=hp.free_adjoinRoot
  let : Nontrivial (AdjoinRoot p):=
    (AdjoinRoot.nontrivial_iff_of_monic hp).mpr
      (Polynomial.natDegree_pos_iff_degree_pos.mp hn)
  infer_instance

end MonicRootEtale318
