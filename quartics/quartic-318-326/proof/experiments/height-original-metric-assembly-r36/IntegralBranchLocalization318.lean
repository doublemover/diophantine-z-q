module
public import LocalizationSourceTransport318
public import IntegralBranchDenominatorCover318
public import IntegralBranchFrames318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace IntegralBranchLocalization318
open Polynomial IntegralSourceBranches318
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R:Type*) [CommRing R] (c:Fin 4→Rˣ) (i:Fin 4)
local instance regrouped_commRing : CommRing (RegroupedOrder R c i) := inferInstance
local instance regrouped_algebra : Algebra (BranchBase R c i) (RegroupedOrder R c i) := inferInstance

@[expose] def regroupedToOpen : RegroupedOrder R c i→+*OpenOrder R c i:=
  (localizedSourceEquiv R c i).toRingHom.comp
    (Algebra.TensorProduct.includeRight : RegroupedOrder R c i→ₐ[BranchBase R c i]
      OpenBase R c i⊗[BranchBase R c i]RegroupedOrder R c i).toRingHom
local instance regroupedAlgebra : Algebra (RegroupedOrder R c i) (OpenOrder R c i):=
  (regroupedToOpen R c i).toAlgebra
@[expose] def regroupedEquiv : RegroupedOrder R c i⊗[BranchBase R c i]OpenBase R c i≃ₐ[RegroupedOrder R c i]OpenOrder R c i:=
  { (Algebra.TensorProduct.comm (BranchBase R c i) (RegroupedOrder R c i) (OpenBase R c i)).toRingEquiv.trans
      (localizedSourceEquiv R c i).toRingEquiv with commutes':=by intro z;rfl }
@[expose] def regroupedDenominator : RegroupedOrder R c i:=
  algebraMap (BranchBase R c i) (RegroupedOrder R c i)
    (IntegralBranchChart318.denominator (c i) (IntegralSourceBranches318.contacts R i)
      (otherTwist R c i) (otherContact R i))

lemma regrouped_localization : IsLocalization.Away (regroupedDenominator R c i) (OpenOrder R c i):=by
  let D:=IntegralBranchChart318.denominator (c i) (IntegralSourceBranches318.contacts R i)
    (otherTwist R c i) (otherContact R i)
  letI:IsLocalization.Away (regroupedDenominator R c i)
      (RegroupedOrder R c i⊗[BranchBase R c i]OpenBase R c i):=by
    simpa only [regroupedDenominator,Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (RegroupedOrder R c i)
        (Submonoid.powers D)) (RegroupedOrder R c i⊗[BranchBase R c i]OpenBase R c i))
  exact IsLocalization.isLocalization_of_algEquiv
    (S:=RegroupedOrder R c i⊗[BranchBase R c i]OpenBase R c i) _ (regroupedEquiv R c i)

@[expose] def sourceMap : IntegralSourceBranches318.SourceOrder R c→+*OpenOrder R c i:=
  (regroupedToOpen R c i).comp (sourceRegroup R c i).toRingHom
local instance sourceAlgebra : Algebra (IntegralSourceBranches318.SourceOrder R c) (OpenOrder R c i):=
  (sourceMap R c i).toAlgebra

lemma denominator_compatibility :
    sourceRegroup R c i (IntegralBranchDenominatorCover318.denominator R c i) =
      regroupedDenominator R c i :=
  IntegralBranchDenominatorCover318.regroup_denominator R c i

lemma source_localization :
    IsLocalization.Away (IntegralBranchDenominatorCover318.denominator R c i) (OpenOrder R c i):=by
  letI:IsLocalization.Away (sourceRegroup R c i (IntegralBranchDenominatorCover318.denominator R c i))
      (OpenOrder R c i):=by
    rw [denominator_compatibility]
    exact regrouped_localization R c i
  exact LocalizationSourceTransport318.away (sourceRegroup R c i).toRingEquiv
    (IntegralBranchDenominatorCover318.denominator R c i) (fun _=>rfl)

lemma sourceMap_on_polynomial (p:R[X]) :
    sourceMap R c i (algebraMap R[X] (IntegralSourceBranches318.SourceOrder R c) p)=
      algebraMap (OpenBase R c i) (OpenOrder R c i) (algebraMap R[X] (OpenBase R c i) p):=by
  change localizedSourceEquiv R c i
    (Algebra.TensorProduct.includeRight
      (sourceRegroup R c i (algebraMap R[X] (IntegralSourceBranches318.SourceOrder R c) p)))=_
  rw [AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply R[X] (BranchBase R c i) (RegroupedOrder R c i)]
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply (BranchBase R c i) (OpenBase R c i)
    (OpenBase R c i⊗[BranchBase R c i]RegroupedOrder R c i),AlgEquiv.commutes]
  rw [←IsScalarTower.algebraMap_apply R[X] (BranchBase R c i) (OpenBase R c i)]

lemma sourceMap_commutes (r : R) :
    sourceMap R c i (algebraMap R (IntegralSourceBranches318.SourceOrder R c) r) =
      algebraMap R (OpenOrder R c i) r := by
  rw [IsScalarTower.algebraMap_apply R R[X] (IntegralSourceBranches318.SourceOrder R c),
    sourceMap_on_polynomial,
    ←IsScalarTower.algebraMap_apply R R[X] (OpenBase R c i),
    ←IsScalarTower.algebraMap_apply R (OpenBase R c i) (OpenOrder R c i)]

local instance sourceTower :
    IsScalarTower R (IntegralSourceBranches318.SourceOrder R c) (OpenOrder R c i) :=
  IsScalarTower.of_algebraMap_eq (fun r => (sourceMap_commutes R c i r).symm)

/-- The full original source's principal open, with its actual integral
scalar structure, is precisely the whole explicit finite-branch chart. -/
@[expose] def sourceLocalizationEquiv :
    Localization.Away (IntegralBranchDenominatorCover318.denominator R c i)≃ₐ[R]OpenOrder R c i:=by
  letI:=source_localization R c i
  exact (IsLocalization.algEquiv (Submonoid.powers (IntegralBranchDenominatorCover318.denominator R c i))
    (Localization.Away (IntegralBranchDenominatorCover318.denominator R c i)) (OpenOrder R c i)).restrictScalars R

@[simp] lemma sourceLocalizationEquiv_on_source (z:IntegralSourceBranches318.SourceOrder R c) :
    sourceLocalizationEquiv R c i
      (algebraMap (IntegralSourceBranches318.SourceOrder R c)
        (Localization.Away (IntegralBranchDenominatorCover318.denominator R c i)) z)=sourceMap R c i z:=by
  letI:=source_localization R c i
  exact (IsLocalization.algEquiv (Submonoid.powers (IntegralBranchDenominatorCover318.denominator R c i))
    (Localization.Away (IntegralBranchDenominatorCover318.denominator R c i)) (OpenOrder R c i)).commutes z


/-- Each principal open of the original integral affine source carries its
actual ramified-coordinate frame. Together with span_top this gives a finite
cover by genuine integral differential frames away from 2,3,5,7. -/
@[expose] def sourceFrame (h2 : IsUnit (2 : R)) :
    KaehlerDifferential R (Localization.Away (IntegralBranchDenominatorCover318.denominator R c i))
      ≃ₗ[Localization.Away (IntegralBranchDenominatorCover318.denominator R c i)]
        Localization.Away (IntegralBranchDenominatorCover318.denominator R c i) :=
  EtaleDifferentialFrame318.ofAlgEquiv (sourceLocalizationEquiv R c i).symm
    (IntegralBranchFrames318.frame R c i h2)

end IntegralBranchLocalization318
