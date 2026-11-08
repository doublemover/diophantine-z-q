module
public import LocalizationSourceTransport318
public import SourceDenominatorCover318
public section
noncomputable section
namespace SourceBranchLocalization318
open Polynomial SourceFiniteBranch318
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) (i:Fin 4)
local instance regrouped_commRing : CommRing (RegroupedOrder c i) := inferInstance
local instance regrouped_algebra : Algebra (BranchBase c i) (RegroupedOrder c i) := inferInstance

@[expose] def regroupedToOpen : RegroupedOrder c i→+*OpenOrder c i:=
  (localizedSourceEquiv c i).toRingHom.comp
    (Algebra.TensorProduct.includeRight : RegroupedOrder c i→ₐ[BranchBase c i]
      OpenBase c i⊗[BranchBase c i]RegroupedOrder c i).toRingHom
local instance regroupedAlgebra : Algebra (RegroupedOrder c i) (OpenOrder c i):=
  (regroupedToOpen c i).toAlgebra
@[expose] def regroupedEquiv : RegroupedOrder c i⊗[BranchBase c i]OpenBase c i≃ₐ[RegroupedOrder c i]OpenOrder c i:=
  { (Algebra.TensorProduct.comm (BranchBase c i) (RegroupedOrder c i) (OpenBase c i)).toRingEquiv.trans
      (localizedSourceEquiv c i).toRingEquiv with commutes':=by intro z;rfl }
@[expose] def regroupedDenominator : RegroupedOrder c i:=
  algebraMap (BranchBase c i) (RegroupedOrder c i)
    (FiniteBranchChart318.denominator (c i) (LinearContactSquareclass318.contacts i)
      (otherTwist c i) (otherContact i))

lemma regrouped_localization : IsLocalization.Away (regroupedDenominator c i) (OpenOrder c i):=by
  let D:=FiniteBranchChart318.denominator (c i) (LinearContactSquareclass318.contacts i)
    (otherTwist c i) (otherContact i)
  letI:IsLocalization.Away (regroupedDenominator c i)
      (RegroupedOrder c i⊗[BranchBase c i]OpenBase c i):=by
    simpa only [regroupedDenominator,Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (RegroupedOrder c i)
        (Submonoid.powers D)) (RegroupedOrder c i⊗[BranchBase c i]OpenBase c i))
  exact IsLocalization.isLocalization_of_algEquiv
    (S:=RegroupedOrder c i⊗[BranchBase c i]OpenBase c i) _ (regroupedEquiv c i)

@[expose] def sourceMap : ContactKummerOrder318.SourceOrder c→+*OpenOrder c i:=
  (regroupedToOpen c i).comp (sourceRegroup c i).toRingHom
local instance sourceAlgebra : Algebra (ContactKummerOrder318.SourceOrder c) (OpenOrder c i):=
  (sourceMap c i).toAlgebra

lemma denominator_compatibility :
    sourceRegroup c i (SourceDenominatorCover318.denominator c i)=regroupedDenominator c i:=by
  rw [SourceDenominatorCover318.denominator,AlgEquiv.commutes]
  simp only [SourceDenominatorCover318.twisted,regroupedDenominator,FiniteBranchChart318.denominator,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact IsScalarTower.algebraMap_apply ℚ[X] (BranchBase c i) (RegroupedOrder c i)
    (ContactKummerOrder318.coefficient c (FourRootPivot318.indices i j.succ))

lemma source_localization :
    IsLocalization.Away (SourceDenominatorCover318.denominator c i) (OpenOrder c i):=by
  letI:IsLocalization.Away (sourceRegroup c i (SourceDenominatorCover318.denominator c i))
      (OpenOrder c i):=by
    rw [denominator_compatibility]
    exact regrouped_localization c i
  exact LocalizationSourceTransport318.away (sourceRegroup c i).toRingEquiv
    (SourceDenominatorCover318.denominator c i) (fun _=>rfl)

local instance sourceTower : IsScalarTower ℚ (ContactKummerOrder318.SourceOrder c) (OpenOrder c i):=
  IsScalarTower.of_algebraMap_eq (fun q=>(RingHom.map_rat_algebraMap (sourceMap c i) q).symm)

/-- The full original source's principal open, with its actual rational
scalar structure, is precisely the whole explicit finite-branch chart. -/
@[expose] def sourceLocalizationEquiv :
    Localization.Away (SourceDenominatorCover318.denominator c i)≃ₐ[ℚ]OpenOrder c i:=by
  letI:=source_localization c i
  exact (IsLocalization.algEquiv (Submonoid.powers (SourceDenominatorCover318.denominator c i))
    (Localization.Away (SourceDenominatorCover318.denominator c i)) (OpenOrder c i)).restrictScalars ℚ

@[simp] lemma sourceLocalizationEquiv_on_source (z:ContactKummerOrder318.SourceOrder c) :
    sourceLocalizationEquiv c i
      (algebraMap (ContactKummerOrder318.SourceOrder c)
        (Localization.Away (SourceDenominatorCover318.denominator c i)) z)=sourceMap c i z:=by
  letI:=source_localization c i
  exact (IsLocalization.algEquiv (Submonoid.powers (SourceDenominatorCover318.denominator c i))
    (Localization.Away (SourceDenominatorCover318.denominator c i)) (OpenOrder c i)).commutes z

lemma sourceMap_on_polynomial (p:ℚ[X]) :
    sourceMap c i (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) p)=
      algebraMap (OpenBase c i) (OpenOrder c i) (algebraMap ℚ[X] (OpenBase c i) p):=by
  change localizedSourceEquiv c i
    (Algebra.TensorProduct.includeRight
      (sourceRegroup c i (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) p)))=_
  rw [AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply ℚ[X] (BranchBase c i) (RegroupedOrder c i)]
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply (BranchBase c i) (OpenBase c i)
    (OpenBase c i⊗[BranchBase c i]RegroupedOrder c i),AlgEquiv.commutes]
  rw [←IsScalarTower.algebraMap_apply ℚ[X] (BranchBase c i) (OpenBase c i)]

end SourceBranchLocalization318
