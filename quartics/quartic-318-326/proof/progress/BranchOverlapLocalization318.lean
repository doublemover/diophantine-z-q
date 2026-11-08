module
public import SourceInfinityOverlap318
public import SourceDenominatorCover318
public section
noncomputable section
namespace BranchOverlapLocalization318
open Polynomial
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
abbrev R:=ℚ[X]
abbrev Whole:=ContactKummerOrder318.SourceOrder c
abbrev Overlap:=ContactKummerOrder318.OpenOrder c
abbrev Branch (i:Fin 4):=Localization.Away (SourceDenominatorCover318.denominator c i)
local instance overlapAlgebra : Algebra (Whole c) (Overlap c):=(SourceOpenFractionField318.orderToOpen c).toAlgebra

/-- Every actual branch denominator is a unit in the entire original
unbranched order. -/
theorem denominator_unit (i:Fin 4):
    IsUnit (SourceOpenFractionField318.orderToOpen c (SourceDenominatorCover318.denominator c i)):=by
  rw [SourceDenominatorCover318.denominator,SourceOpenFractionField318.orderToOpen_on_polynomial]
  simp only [SourceDenominatorCover318.twisted,map_prod]
  apply IsUnit.prod_univ_iff.mpr
  intro j
  exact (ContactKummerOrder318.coefficient_unit c _).map _

@[expose] def toOpen (i:Fin 4):Branch c i→+*Overlap c:=
  IsLocalization.Away.lift (g:=SourceOpenFractionField318.orderToOpen c)
    (SourceDenominatorCover318.denominator c i) (denominator_unit c i)

@[simp] theorem toOpen_on_source (i:Fin 4) (x:Whole c):
    toOpen c i (algebraMap (Whole c) (Branch c i) x)=SourceOpenFractionField318.orderToOpen c x:=
  IsLocalization.Away.lift_eq _ _ _

local instance branchAlgebra (i:Fin 4):Algebra (Branch c i) (Overlap c):=(toOpen c i).toAlgebra
local instance overlapSMul : SMul (Whole c) (Overlap c):=(overlapAlgebra c).toSMul
local instance overlapModule : Module (Whole c) (Overlap c):=Algebra.toModule
local instance branchTower (i:Fin 4):IsScalarTower (Whole c) (Branch c i) (Overlap c):=
  IsScalarTower.of_algebraMap_eq (fun x=>(toOpen_on_source c i x).symm)

@[expose] def factor (i:Fin 4):Whole c:=
  algebraMap R (Whole c) (X-C (LinearContactSquareclass318.contacts i))

theorem denominator_factor (i:Fin 4):ContactKummerOrder318.denominator=
    (X-C (LinearContactSquareclass318.contacts i))*SourceDenominatorCover318.untwisted i:=by
  fin_cases i <;> simp [ContactKummerOrder318.denominator,SourceDenominatorCover318.untwisted,
    FourRootPivot318.indices,LinearContactSquareclass318.contacts,Fin.prod_univ_succ] <;> ring

theorem factor_product (i:Fin 4):
    factor c i*SourceDenominatorCover318.denominator c i=
      algebraMap ℚ (Whole c) (SourceDenominatorCover318.twistUnit c i:ℚ)*SourceOpenFractionField318.d c:=by
  have h:(X-C (LinearContactSquareclass318.contacts i))*SourceDenominatorCover318.twisted c i=
      C (SourceDenominatorCover318.twistUnit c i:ℚ)*ContactKummerOrder318.denominator:=by
    rw [SourceDenominatorCover318.twisted_factor,denominator_factor]
    ring
  change algebraMap R (Whole c) _*algebraMap R (Whole c) _=_*algebraMap R (Whole c) _
  rw [←map_mul,h,map_mul]
  congr 1

theorem whole_localization (i:Fin 4):
    IsLocalization.Away (algebraMap (Whole c) (Branch c i) (factor c i)) (Overlap c):=by
  letI:=SourceOpenFractionField318.open_isLocalization c
  letI:IsLocalization.Away (factor c i*SourceDenominatorCover318.denominator c i) (Overlap c):=by
    apply IsLocalization.Away.of_associated (r:=SourceOpenFractionField318.d c)
    rw [factor_product]
    exact associated_unit_mul_right _ _
      ((SourceDenominatorCover318.twistUnit c i).isUnit.map (algebraMap ℚ (Whole c)))
  exact ReciprocalOverlapBase318.away_of_mul (factor c i) (SourceDenominatorCover318.denominator c i)

/-- The map from each entire branch chart to the full overlap is its actual
principal localization away from the remaining contact, not a generic map. -/
@[expose] def overlapEquiv (i:Fin 4):
    Localization.Away (algebraMap (Whole c) (Branch c i) (factor c i))≃ₐ[Branch c i]Overlap c:=by
  letI:=whole_localization c i
  exact IsLocalization.algEquiv
    (Submonoid.powers (algebraMap (Whole c) (Branch c i) (factor c i))) _ _
end BranchOverlapLocalization318
