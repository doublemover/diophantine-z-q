module
public import ActualLinearRootDifferent318
public import FourRootActualTraceDifferentSupport318
public import FourRootActualBranchKaehler318
public section
noncomputable section
namespace FourRootActualDifferentTower318
open Polynomial FourRootActualFiniteBranchChart318 FourRootActualFractionField318
open scoped TensorProduct
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (i:Fin 4)
local instance polyAlgebra:Algebra ℂ[X] (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance branchDedekind:IsDedekindDomain (BranchBase b i):=ActualLinearRootDifferent318.dedekind (b i)
@[expose] def branchMap:BranchBase b i→+*A b:=
  (sourceRegroup b i).symm.toRingHom.comp (algebraMap (BranchBase b i) (RegroupedOrder b i))
local instance branchAlgebra:Algebra (BranchBase b i) (A b):=(branchMap b i).toAlgebra
local instance baseTower:IsScalarTower ℂ[X] (BranchBase b i) (A b):=by
  apply IsScalarTower.of_algebraMap_eq
  intro p
  change algebraMap ℂ[X] (A b) p=(sourceRegroup b i).symm
    (algebraMap (BranchBase b i) (RegroupedOrder b i)
      (algebraMap ℂ[X] (BranchBase b i) p))
  rw [←IsScalarTower.algebraMap_apply,AlgEquiv.commutes]
@[expose] def branchEquiv:A b≃ₐ[BranchBase b i]RegroupedOrder b i where
  __:=(sourceRegroup b i).toRingEquiv
  commutes' x:=by
    change sourceRegroup b i ((sourceRegroup b i).symm _)=_
    exact (sourceRegroup b i).apply_symm_apply _
lemma relative_finite_free:
    Module.Finite (BranchBase b i) (A b)∧Module.Free (BranchBase b i) (A b):=by
  let T:=ThreeRootOrder318.Order (FiniteBranchChart318.other twists (otherBranch b i))
  letI:Module.Finite ℂ[X] T:=(ThreeRootOrder318.finite_free _).1
  letI:Module.Free ℂ[X] T:=(ThreeRootOrder318.finite_free _).2
  letI:Module.Finite (BranchBase b i) (RegroupedOrder b i):=inferInstance
  letI:Module.Free (BranchBase b i) (RegroupedOrder b i):=inferInstance
  exact ⟨Module.Finite.equiv (branchEquiv b i).symm.toLinearEquiv,
    Module.Free.of_equiv (branchEquiv b i).symm.toLinearEquiv⟩
local instance relativeFinite:Module.Finite (BranchBase b i) (A b):=(relative_finite_free b i).1
local instance relativeFree:Module.Free (BranchBase b i) (A b):=(relative_finite_free b i).2
local instance affineFinite:Module.Finite ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free b).1
local instance affineFree:Module.Free ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free b).2
local instance branchFinite:Module.Finite ℂ[X] (BranchBase b i):=
  Module.Finite.of_basis (ActualLinearRootDifferent318.basis (b i))
local instance branchFree:Module.Free ℂ[X] (BranchBase b i):=
  Module.Free.of_basis (ActualLinearRootDifferent318.basis (b i))
lemma branchMap_root:
    branchMap b i (ActualLinearRootDifferent318.root (b i))=
      FourRootAffineCoordinateRing318.coordinate b (some i):=by
  apply (sourceRegroup b i).injective
  change sourceRegroup b i ((sourceRegroup b i).symm _)=_
  rw [AlgEquiv.apply_symm_apply,FourRootActualBranchKaehler318.regroup_root]
  rw [FourRootActualBranchKaehler318.baseCoordinate_root]
  rfl

/-- Exact transitivity of the TRACE-defined different in the genuine
whole-order tower C[t] → C[z_i] → A. The first factor is still the actual
relative different, not silently replaced by the unit ideal globally. -/
theorem actual_factorization:
    differentIdeal ℂ[X] (A b)=
      differentIdeal (BranchBase b i) (A b)*
        Ideal.span {2*FourRootAffineCoordinateRing318.coordinate b (some i)}:=by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (A:=ℂ[X])
    (B:=BranchBase b i) (A b)]
  rw [ActualLinearRootDifferent318.different_eq,Ideal.map_span]
  simp only [Set.image_singleton,map_mul,map_ofNat]
  change _=_*Ideal.span {2*branchMap b i (ActualLinearRootDifferent318.root (b i))}
  rw [branchMap_root]
end FourRootActualDifferentTower318
