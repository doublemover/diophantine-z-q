module
public import SelectedHorizontalOriginalScalar318
public import SelectedHorizontalNormalDual318
public import SelectedNormalTraceLocalization318
public import SelectedMonogenicUnitNormalTrace318
public import Mathlib.Tactic.Ring
public section
noncomputable section

open Polynomial SelectedPrincipalPrimeNormalIntersection318
open SelectedHorizontalOriginalScalar318 SelectedHorizontalNormalDual318
open SelectedNormalTraceLocalization318 SelectedMonogenicUnitNormalTrace318
open SelectedTraceDualNormalization318

namespace SelectedActualHorizontalPolynomialTrace318

variable {O K F : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
variable [Field K] [Algebra O[X] K] [IsFractionRing O[X] K]
variable [Field F] [Algebra K F] [Algebra O[X] F] [IsScalarTower O[X] K F]
variable [FiniteDimensional K F] [Algebra.IsSeparable K F]
variable (q : PrimeSpectrum O[X]) (hq : principalPrime q)
variable (hor : ∀ b : O, b≠0 → C b∉q.asIdeal)

attribute [local instance] SelectedPrincipalPrimeNormalIntersection318.localAlgebra

local notation "R" => localRing q
local notation "jF" => algebraMap O[X] F X

include hq hor in
/-- All horizontal primes on the literal arithmetic affine J-line,
including exact J=0 and J=1728. Outside those two the same original
monic derivative unit gives trace regularity. At a collision the
corresponding literal factor clears trace in the genuine residue
characteristic zero chart. -/
theorem numerator_integral_horizontal
    (M : ℕ) (hM : M≠0) (p : (OpenJModel318.Base M)[X]) (hp : p.Monic)
    (hu : IsUnit (AdjoinRoot.mk p p.derivative))
    (c : OpenJModel318.Base M →+* K)
    (hc : c (OpenJModel318.jCoord M)=algebraMap O[X] K X)
    (ξ : F) (hg : Algebra.adjoin K ({ξ}:Set F)=⊤) (hmin : p.map c=minpoly K ξ)
    (x : F) (hx : x∈complementary K (integralClosure O[X] F)) :
    letI : Algebra (localRing q) F := Algebra.compHom F (algebraMap (localRing q) K)
    IsIntegral (localRing q) (((M:F)*jF*(jF-1728))*x) := by
  letI : Algebra R F := Algebra.compHom F (algebraMap R K)
  letI : IsScalarTower R K F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower O[X] R F :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (IsScalarTower.algebraMap_apply O[X] K F a).trans
        (congrArg (algebraMap K F) (IsScalarTower.algebraMap_apply O[X] R K a)))
  letI : IsDiscreteValuationRing R := local_isDVR q hq
  letI : IsIntegrallyClosed R := isIntegrallyClosed_of_isLocalization R q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors
  letI : CharZero (IsLocalRing.ResidueField R) := horizontal_residueCharZero q hor
  have hLocal : x∈complementary K (integralClosure R F) :=
    global_mem_local q.asIdeal.primeCompl hx
  have hj : algebraMap R F (localJ q)=jF :=
    (IsScalarTower.algebraMap_apply O[X] R F (X:O[X])).symm
  have hJ : jF∈integralClosure R F := hj ▸ (integralClosure R F).algebraMap_mem (localJ q)
  have hB : jF-1728∈integralClosure R F := by
    have h1728 : (1728:F)∈integralClosure R F := (integralClosure R F).natCast_mem 1728
    exact sub_mem hJ h1728
  have hC : (M:F)∈integralClosure R F := (integralClosure R F).natCast_mem M
  apply (mem_integralClosure_iff R F).mp
  by_cases h0 : (X:O[X])∈q.asIdeal
  · have hz : jF*x∈integralClosure R F := by
      have h := clears_of_residueCharZero (K:=K) (F:=F) (localJ q) (localJ_mem q h0) x hLocal
      rwa [hj] at h
    convert mul_mem (mul_mem hC hB) hz using 1 <;> ring
  by_cases h1728 : (X-1728:O[X])∈q.asIdeal
  · have hz : (jF-1728)*x∈integralClosure R F := by
      have h := clears_of_residueCharZero (K:=K) (F:=F) (localJ q-1728)
        (localJ_sub_mem q h1728) x hLocal
      rwa [map_sub,map_ofNat,hj] at h
    convert mul_mem (mul_mem hC hJ) hz using 1 <;> ring
  · let cR := localScalar q hor M hM h0 h1728
    let pR := p.map cR
    have hm : pR.map (algebraMap R K)=minpoly K ξ := by
      change (p.map cR).map (algebraMap R K)=_
      rw [Polynomial.map_map,matches_global q hor M hM h0 h1728 c hc,hmin]
    have hξ : IsIntegral R ξ := by
      have h : aeval ξ (pR.map (algebraMap R K))=0 := by rw [hm]; exact minpoly.aeval K ξ
      rw [aeval_map_algebraMap] at h
      exact ⟨pR,hp.map _,h⟩
    have huR : IsUnit (AdjoinRoot.mk pR pR.derivative) :=
      derivative_unit_map cR p hu
    have hx0 : x∈integralClosure R F :=
      normal_dual_of_derivative_unit hg hξ pR hm huR x hLocal
    exact mul_mem (mul_mem (mul_mem hC hJ) hB) hx0

end SelectedActualHorizontalPolynomialTrace318

#print axioms SelectedActualHorizontalPolynomialTrace318.numerator_integral_horizontal
