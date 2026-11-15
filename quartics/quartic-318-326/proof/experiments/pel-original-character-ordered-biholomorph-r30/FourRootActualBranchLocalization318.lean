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
  letI:IsLocalization.Away D (OpenBase b i):=by
    change IsLocalization.Away
      (FiniteBranchChart318.denominator (1:ℂˣ) (b i) twists (otherBranch b i))
      (Localization.Away (FiniteBranchChart318.denominator (1:ℂˣ) (b i) twists (otherBranch b i)))
    infer_instance
  letI:IsLocalization.Away (regroupedDenominator b i)
      (RegroupedOrder b i⊗[BranchBase b i]OpenBase b i):=by
    simpa only [regroupedDenominator,Algebra.algebraMapSubmonoid_powers] using
      (IsLocalization.tensor (S:=RegroupedOrder b i) (A:=OpenBase b i)
        (Submonoid.powers D))
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

/-- Abstract proof with the EXISTING R-actions supplied independently.
No Algebra.toSMul dictionary for R on A or B is substituted. The concrete
sourceTower below applies this opaque lemma instead of kernel-checking a
large expanded quotient/tensor proof term. -/
private theorem scalarTowerFromCompatibleMap
    (R P A C B:Type*) [CommRing R] [CommRing P] [CommRing A]
    [CommRing C] [CommRing B] [Algebra R P] [Algebra P A]
    [SMul R A] [IsScalarTower R P A] [Algebra R C] [Algebra C B]
    [SMul R B] [IsScalarTower R C B] [Algebra A B]
    (hmap:∀r:R,algebraMap A B (algebraMap P A (algebraMap R P r))=
      algebraMap C B (algebraMap R C r)):IsScalarTower R A B:=by
  refine ⟨fun r a z=>?_⟩
  rw [Algebra.smul_def (R:=A) (A:=B) (r • a) z,
    Algebra.smul_def (R:=A) (A:=B) a z]
  have hca:(r • a:A)=algebraMap P A (algebraMap R P r)*a:=by
    calc
      r • a = (algebraMap R P r) • a :=
        (IsScalarTower.algebraMap_smul (R:=R) P r a).symm
      _ = algebraMap P A (algebraMap R P r)*a :=
        Algebra.smul_def (R:=P) (A:=A) _ _
  rw [hca,map_mul,hmap,mul_assoc]
  calc
    _=(algebraMap R C r) • (algebraMap A B a*z):=(Algebra.smul_def (R:=C) (A:=B) _ _).symm
    _=r • (algebraMap A B a*z):=
      IsScalarTower.algebraMap_smul (R:=R) C r (algebraMap A B a*z)

/-- The already proved polynomial-map square specialized to actual complex
scalars; the original map and both scalar actions are unchanged. -/
lemma sourceMap_on_complex (c:ℂ):
    sourceMap b i (algebraMap ℂ[X] (FourRootActualFractionField318.A b)
      (algebraMap ℂ ℂ[X] c))=
      algebraMap (OpenBase b i) (OpenOrder b i) (algebraMap ℂ (OpenBase b i) c):=by
  have h:=sourceMap_on_polynomial b i (algebraMap ℂ ℂ[X] c)
  rw [←IsScalarTower.algebraMap_apply ℂ ℂ[X] (OpenBase b i)] at h
  exact h

/-- The same genuine source tower, proved by typed opaque helper application
rather than expanding its full quotient/tensor dictionaries in one proof. -/
local instance sourceTower : IsScalarTower ℂ (FourRootActualFractionField318.A b) (OpenOrder b i):=
  scalarTowerFromCompatibleMap ℂ ℂ[X] (FourRootActualFractionField318.A b)
    (OpenBase b i) (OpenOrder b i) (sourceMap_on_complex b i)

/-- Name the SAME source-linear localization equivalence before restricting
scalars, so later coherence checks reuse this exact map instead of expanding
separate large localization-instance constructions. -/
@[expose] def sourceLocalizationAlgEquiv :
    Localization.Away (FourRootActualFiniteBranchChart318.denominator b i)≃ₐ[FourRootActualFractionField318.A b]OpenOrder b i:=by
  letI:=source_localization b i
  exact IsLocalization.algEquiv (Submonoid.powers (FourRootActualFiniteBranchChart318.denominator b i))
    (Localization.Away (FourRootActualFiniteBranchChart318.denominator b i)) (OpenOrder b i)

/-- The full original source's principal open, with its actual complex
scalar structure, is precisely the whole explicit finite-branch chart. -/
@[expose] def sourceLocalizationEquiv :
    Localization.Away (FourRootActualFiniteBranchChart318.denominator b i)≃ₐ[ℂ]OpenOrder b i:=
  (sourceLocalizationAlgEquiv b i).restrictScalars ℂ

@[simp] lemma sourceLocalizationEquiv_on_source (z:FourRootActualFractionField318.A b) :
    sourceLocalizationEquiv b i
      (algebraMap (FourRootActualFractionField318.A b)
        (Localization.Away (FourRootActualFiniteBranchChart318.denominator b i)) z)=sourceMap b i z:=
  (sourceLocalizationAlgEquiv b i).commutes z


end FourRootActualBranchLocalization318
