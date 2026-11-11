module
public import LocalizationSourceTransport318
public import FourRootActualFiniteBranchChart318
public section
noncomputable section
namespace FourRootActualBranchLocalization318
open Polynomial FourRootActualFiniteBranchChart318
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (b:Fin 4→ℂ) (i:Fin 4)
local instance polyAlgebra:Algebra ℂ[X] (FourRootActualFractionField318.A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance polyTower:IsScalarTower ℂ ℂ[X] (FourRootActualFractionField318.A b):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm
local instance regrouped_commRing : CommRing (RegroupedOrder b i) := inferInstance
local instance regrouped_algebra : Algebra (BranchBase b i) (RegroupedOrder b i) := inferInstance

@[expose] def regroupedToOpen : RegroupedOrder b i→+*OpenOrder b i:=
  (localizedSourceEquiv b i).toRingHom.comp
    (Algebra.TensorProduct.includeRight : RegroupedOrder b i→ₐ[BranchBase b i]
      OpenBase b i⊗[BranchBase b i]RegroupedOrder b i).toRingHom
local instance regroupedAlgebra : Algebra (RegroupedOrder b i) (OpenOrder b i):=
  (regroupedToOpen b i).toAlgebra
@[expose] def regroupedEquiv : RegroupedOrder b i⊗[BranchBase b i]OpenBase b i≃ₐ[RegroupedOrder b i]OpenOrder b i:=
  { (Algebra.TensorProduct.comm (BranchBase b i) (RegroupedOrder b i) (OpenBase b i)).toRingEquiv.trans
      (localizedSourceEquiv b i).toRingEquiv with commutes':=by intro z;rfl }
@[expose] def regroupedDenominator : RegroupedOrder b i:=
  algebraMap (BranchBase b i) (RegroupedOrder b i)
    (branchDenominator b i)

lemma regrouped_localization : IsLocalization.Away (regroupedDenominator b i) (OpenOrder b i):=by
  let D:=branchDenominator b i
  letI:IsLocalization.Away (regroupedDenominator b i)
      (RegroupedOrder b i⊗[BranchBase b i]OpenBase b i):=by
    simpa only [regroupedDenominator,Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (RegroupedOrder b i)
        (Submonoid.powers D)) (RegroupedOrder b i⊗[BranchBase b i]OpenBase b i))
  exact IsLocalization.isLocalization_of_algEquiv
    (S:=RegroupedOrder b i⊗[BranchBase b i]OpenBase b i) _ (regroupedEquiv b i)

@[expose] def sourceMap : FourRootActualFractionField318.A b→+*OpenOrder b i:=
  (regroupedToOpen b i).comp (sourceRegroup b i).toRingHom
local instance sourceAlgebra : Algebra (FourRootActualFractionField318.A b) (OpenOrder b i):=
  (sourceMap b i).toAlgebra

lemma denominator_compatibility :
    sourceRegroup b i (FourRootActualFiniteBranchChart318.denominator b i)=regroupedDenominator b i:=
  denominator_regroup b i

lemma source_localization :
    IsLocalization.Away (FourRootActualFiniteBranchChart318.denominator b i) (OpenOrder b i):=by
  letI:IsLocalization.Away (sourceRegroup b i (FourRootActualFiniteBranchChart318.denominator b i))
      (OpenOrder b i):=by
    rw [denominator_compatibility]
    exact regrouped_localization b i
  exact LocalizationSourceTransport318.away (sourceRegroup b i).toRingEquiv
    (FourRootActualFiniteBranchChart318.denominator b i) (fun _=>rfl)

/-- Complex scalars are inherited through the genuine polynomial-base
maps, not justified by the rational-only universal ring hom argument. -/
local instance sourceTower : IsScalarTower ℂ (FourRootActualFractionField318.A b) (OpenOrder b i):=by
  apply IsScalarTower.of_algebraMap_eq
  intro z
  change algebraMap ℂ (OpenOrder b i) z=sourceMap b i (algebraMap ℂ (FourRootActualFractionField318.A b) z)
  unfold sourceMap regroupedToOpen
  simp only [RingHom.comp_apply]
  rw [show algebraMap ℂ (FourRootActualFractionField318.A b) z=
    algebraMap ℂ[X] (FourRootActualFractionField318.A b) (C z) from (Polynomial.aeval_C _ z).symm,
    AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply ℂ[X] (BranchBase b i) (RegroupedOrder b i),
    AlgHom.commutes,IsScalarTower.algebraMap_apply (BranchBase b i) (OpenBase b i)
      (OpenBase b i⊗[BranchBase b i]RegroupedOrder b i),AlgEquiv.commutes]
  simp only [←IsScalarTower.algebraMap_apply]
  rfl

/-- The full original source's principal open, with its actual complex
scalar structure, is precisely the whole explicit finite-branch chart. -/
@[expose] def sourceLocalizationEquiv :
    Localization.Away (FourRootActualFiniteBranchChart318.denominator b i)≃ₐ[ℂ]OpenOrder b i:=by
  letI:=source_localization b i
  exact (IsLocalization.algEquiv (Submonoid.powers (FourRootActualFiniteBranchChart318.denominator b i))
    (Localization.Away (FourRootActualFiniteBranchChart318.denominator b i)) (OpenOrder b i)).restrictScalars ℂ

@[simp] lemma sourceLocalizationEquiv_on_source (z:FourRootActualFractionField318.A b) :
    sourceLocalizationEquiv b i
      (algebraMap (FourRootActualFractionField318.A b)
        (Localization.Away (FourRootActualFiniteBranchChart318.denominator b i)) z)=sourceMap b i z:=by
  letI:=source_localization b i
  exact (IsLocalization.algEquiv (Submonoid.powers (FourRootActualFiniteBranchChart318.denominator b i))
    (Localization.Away (FourRootActualFiniteBranchChart318.denominator b i)) (OpenOrder b i)).commutes z

lemma sourceMap_on_polynomial (p:ℂ[X]) :
    sourceMap b i (algebraMap ℂ[X] (FourRootActualFractionField318.A b) p)=
      algebraMap (OpenBase b i) (OpenOrder b i) (algebraMap ℂ[X] (OpenBase b i) p):=by
  change localizedSourceEquiv b i
    (Algebra.TensorProduct.includeRight
      (sourceRegroup b i (algebraMap ℂ[X] (FourRootActualFractionField318.A b) p)))=_
  rw [AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply ℂ[X] (BranchBase b i) (RegroupedOrder b i)]
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply (BranchBase b i) (OpenBase b i)
    (OpenBase b i⊗[BranchBase b i]RegroupedOrder b i),AlgEquiv.commutes]
  rw [←IsScalarTower.algebraMap_apply ℂ[X] (BranchBase b i) (OpenBase b i)]

end FourRootActualBranchLocalization318
