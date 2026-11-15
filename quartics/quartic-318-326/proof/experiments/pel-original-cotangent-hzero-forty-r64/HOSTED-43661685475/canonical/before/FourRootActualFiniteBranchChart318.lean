module
public import FourRootActualFractionField318
public import FiniteBranchChart318
public import FourRootPivot318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace FourRootActualFiniteBranchChart318
open Polynomial FourRootPivot318 FourRootAffineTensorPresentation318
open FourRootActualFractionField318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
variable (b:Fin 4→ℂ) (i:Fin 4)
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance polyTower:IsScalarTower ℂ P (A b):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm
@[expose] def twists:Fin 3→ℂˣ:=fun _=>1
@[expose] def otherBranch (j:Fin 3):ℂ:=b (indices i j.succ)
abbrev BranchBase:=FiniteBranchChart318.BranchBase (1:ℂˣ) (b i)
abbrev OpenBase:=FiniteBranchChart318.OpenBase (1:ℂˣ) (b i) twists (otherBranch b i)
abbrev OpenOrder:=FiniteBranchChart318.OpenOrder (1:ℂˣ) (b i) twists (otherBranch b i)
abbrev RegroupedOrder:=FiniteBranchChart318.OriginalOrder (1:ℂˣ) (b i) twists (otherBranch b i)
local instance regroupedRing:CommRing (RegroupedOrder b i):=inferInstance
local instance regroupedAlgebra:Algebra (BranchBase b i) (RegroupedOrder b i):=inferInstance
lemma other_distinct (hb:Function.Injective b):∀j,b i≠otherBranch b i j:=by
  intro j
  have h:indices i 0≠indices i j.succ:=
    (indices_injective i).ne (by intro h;have hv:=congrArg Fin.val h;simp at hv)
  simpa only [indices_zero,otherBranch] using hb.ne h

/-- This is the actual literal affine quotient, regrouped over its chosen
root, with the unchanged complex-polynomial base retained. -/
@[expose] def sourceRegroup:A b≃ₐ[P]RegroupedOrder b i:=
  (polynomialEquivalence b).trans (by
    simpa only [RegroupedOrder,FiniteBranchChart318.OriginalOrder,
      FiniteBranchChart318.BranchBase,LinearRootCoordinate318.Root,
      FiniteBranchChart318.other,LinearRootCoordinate318.parameter,
      twists,otherBranch,radicand,Units.val_one,map_one,one_mul,indices_zero]
      using FourRootPivot318.regroup (radicand b) i)
@[expose] def localizedSourceEquiv:
    OpenBase b i⊗[BranchBase b i]RegroupedOrder b i≃ₐ[OpenBase b i]OpenOrder b i:=
  FiniteBranchChart318.localizedOrderEquiv (1:ℂˣ) (b i) twists (otherBranch b i)
@[expose] def branchDenominator:BranchBase b i:=
  FiniteBranchChart318.denominator (1:ℂˣ) (b i) twists (otherBranch b i)
@[expose] def denominatorPolynomial:P:=∏j:Fin 3,radicand b (indices i j.succ)
@[expose] def denominator:A b:=algebraMap P (A b) (denominatorPolynomial b i)
lemma denominator_branch:
    branchDenominator b i=algebraMap P (BranchBase b i) (denominatorPolynomial b i):=by
  simp only [branchDenominator,FiniteBranchChart318.denominator,denominatorPolynomial,
    map_prod,FiniteBranchChart318.other,LinearRootCoordinate318.parameter,
    twists,otherBranch,radicand,Units.val_one,map_one,one_mul]
lemma denominator_regroup:
    sourceRegroup b i (denominator b i)=
      algebraMap (BranchBase b i) (RegroupedOrder b i) (branchDenominator b i):=by
  rw [denominator,AlgEquiv.commutes,denominator_branch]
  exact IsScalarTower.algebraMap_apply P (BranchBase b i) (RegroupedOrder b i) _
lemma finite_free_etale:
    Module.Finite (OpenBase b i) (OpenOrder b i) ∧
    Module.Free (OpenBase b i) (OpenOrder b i) ∧
    Algebra.Etale (OpenBase b i) (OpenOrder b i):=
  FiniteBranchChart318.open_finite_free_etale (1:ℂˣ) (b i) twists
    (otherBranch b i) (by norm_num)
@[expose] def root:OpenBase b i:=
  FiniteBranchChart318.openRoot (1:ℂˣ) (b i) twists (otherBranch b i)
lemma exact_square:algebraMap P (OpenBase b i) (X-C (b i))=(root b i)^2:=by
  simpa only [Units.inv_one,Units.val_one,map_one,one_mul,root] using
    FiniteBranchChart318.open_contact_square (1:ℂˣ) (b i) twists (otherBranch b i)
end FourRootActualFiniteBranchChart318
