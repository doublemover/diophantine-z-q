module
public import IntegralFullOverlapLocalization318
public import ReciprocalOverlapBase318
public section
noncomputable section
namespace IntegralEveryBranchLocalization318
open Polynomial
open IntegralSourceBranches318 IntegralBranchDenominatorCover318
open IntegralBranchCoordinates318 IntegralOverlapChartMaps318
open IntegralAllBranchOverlapMaps318 IntegralFullOverlapLocalization318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
local instance overlapCommRing : CommRing (Overlap R c) := inferInstance
local instance sourceCommRing : CommRing (SourceOrder R c) := inferInstance
local instance branchCommRing (i:Fin 4) : CommRing (B R c i) := inferInstance
local instance : Algebra (SourceOrder R c) (Overlap R c) := sourceAlgebra R c
local instance sourceSMul : SMul (SourceOrder R c) (Overlap R c) :=
  (sourceAlgebra R c).toSMul
local instance sourceModule : Module (SourceOrder R c) (Overlap R c) := Algebra.toModule
@[expose] def branchAlgebra (i : Fin 4) : Algebra (B R c i) (Overlap R c) :=
  (show B R c i →+* Overlap R c from (branchMap R c i).toRingHom).toAlgebra
local instance (i : Fin 4) : Algebra (B R c i) (Overlap R c) := branchAlgebra R c i
local instance branchTower (i : Fin 4) :
    IsScalarTower (SourceOrder R c) (B R c i) (Overlap R c) :=
  IsScalarTower.of_algebraMap_eq (R:=SourceOrder R c) (S:=B R c i)
    (A:=Overlap R c) (fun a => by
      change IntegralOverlapOpenImmersions318.sourceMap R c a=
        branchMap R c i (algebraMap (SourceOrder R c) (B R c i) a)
      exact (branchMap_source R c i a).symm)

@[expose] def contactFactor (i : Fin 4) : SourceOrder R c :=
  algebraMap R[X] (SourceOrder R c) (X - C (contacts R i))

theorem factor_product (i : Fin 4) :
    contactFactor R c i * denominator R c i =
      algebraMap R (SourceOrder R c) (twistUnit R c i : R) * sourceQuartic R c := by
  have h := congrArg (algebraMap R[X] (SourceOrder R c))
    (IntegralBranchBicanonical318.factor_product_polynomial R c i)
  have hC (a : R) : algebraMap R[X] (SourceOrder R c) (C a) =
      algebraMap R (SourceOrder R c) a :=
    (IsScalarTower.algebraMap_apply R R[X] (SourceOrder R c) a).symm
  simpa only [map_mul,hC,contactFactor,denominator,sourceQuartic] using h

/-- For each of the four actual contacts, the same common overlap is the
full remaining-contact principal open, with the already constructed branchMap.
This covers all indices without discarding any additional coefficient prime. -/
theorem whole_localization (i : Fin 4) :
    IsLocalization.Away
      (algebraMap (SourceOrder R c) (B R c i) (contactFactor R c i)) (Overlap R c) := by
  letI := IntegralFullOverlapLocalization318.whole_localization R c
  haveI : IsLocalization.Away (contactFactor R c i * denominator R c i) (Overlap R c) := by
    apply IsLocalization.Away.of_associated (S:=Overlap R c) (r := sourceQuartic R c)
    rw [factor_product]
    exact associated_unit_mul_right _ _
      ((twistUnit R c i).isUnit.map (algebraMap R (SourceOrder R c)))
  exact ReciprocalOverlapBase318.away_of_mul
    (R:=SourceOrder R c) (A:=B R c i) (B:=Overlap R c)
    (contactFactor R c i) (denominator R c i)

@[expose] def localizationEquiv (i : Fin 4) :
    Localization.Away (algebraMap (SourceOrder R c) (B R c i) (contactFactor R c i))
      ≃ₐ[B R c i] Overlap R c := by
  letI := whole_localization R c i
  exact IsLocalization.algEquiv
    (Submonoid.powers (algebraMap (SourceOrder R c) (B R c i) (contactFactor R c i)))
    (Localization.Away (algebraMap (SourceOrder R c) (B R c i) (contactFactor R c i)))
    (Overlap R c)

@[simp] theorem localizationEquiv_branch (i : Fin 4) (a : B R c i) :
    localizationEquiv R c i (algebraMap (B R c i)
      (Localization.Away (algebraMap (SourceOrder R c) (B R c i) (contactFactor R c i))) a) =
        branchMap R c i a := by
  change localizationEquiv R c i (algebraMap (B R c i)
    (Localization.Away (algebraMap (SourceOrder R c) (B R c i) (contactFactor R c i))) a)=
      algebraMap (B R c i) (Overlap R c) a
  exact (localizationEquiv R c i).commutes a
end IntegralEveryBranchLocalization318
