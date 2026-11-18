module
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace ActualDvrMeromorphicOrder318
open IsDiscreteValuationRing
/-- The canonical finite/infinite additive-value conversion, preserving
infinity rather than converting the value of zero into an integer. -/
@[expose] def enatToInt : ℕ∞ →+o WithTop ℤ where
  toFun n:=n.map (fun m:ℕ=>(m:ℤ))
  map_zero':=rfl
  map_add' a b:=by
    cases a with
    | top => cases b with
      | top => change (⊤:WithTop ℤ)=⊤+⊤; simp
      | coe b => change (⊤:WithTop ℤ)=⊤+(b:ℤ); simp
    | coe a => cases b with
      | top => change (⊤:WithTop ℤ)=(a:ℤ)+⊤; simp
      | coe b => change (((a+b:ℕ):ℤ):WithTop ℤ)=(a:ℤ)+(b:ℤ); norm_cast
  monotone' := by
    intro a b hab
    cases a with
    | top => cases b with
      | top => exact le_refl _
      | coe b => exact (not_le_of_gt (ENat.coe_lt_top b) hab).elim
    | coe a => cases b with
      | top => exact le_top
      | coe b =>
        change ((a:ℤ):WithTop ℤ)≤(b:ℤ)
        have hh:a≤b := by exact_mod_cast hab
        exact_mod_cast hh
variable (S K:Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Algebra S K] [IsFractionRing S K]
@[expose] def integralValue:AddValuation S (WithTop ℤ):=(addVal S).map enatToInt rfl
lemma integralValue_finite(x:S)(hx:x≠0):
    integralValue S x=((addVal S x).toNat:ℤ):=by
  have htop:addVal S x≠⊤:=fun h=>hx ((addVal_eq_top_iff (R:=S)).mp h)
  change enatToInt (addVal S x)=_
  rw [←ENat.natCast_toNat htop]
  rfl
lemma support:nonZeroDivisors S≤(AddValuation.toValuation (integralValue S)).supp.primeCompl:=by
  intro x hx
  change integralValue S x≠⊤
  rw [integralValue_finite S x (mem_nonZeroDivisors_iff_ne_zero.mp hx)]
  simp
/-- Actual normalized DVR valuation extended to the specified ORIGINAL
fraction field, including negative values for poles. -/
@[expose] def value:AddValuation K (WithTop ℤ):=
  AddValuation.ofValuation ((AddValuation.toValuation (integralValue S)).extendToLocalization
    (support S) K)
lemma value_integral(x:S)(hx:x≠0):
    value S K (algebraMap S K x)=((addVal S x).toNat:ℤ):=by
  change (AddValuation.toValuation (integralValue S)).extendToLocalization
    (support S) K (algebraMap S K x)=_
  rw [Valuation.extendToLocalization_apply_map_apply]
  exact integralValue_finite S x hx
lemma value_unit(x:S)(hx:IsUnit x):value S K (algebraMap S K x)=0:=by
  rw [value_integral S K x hx.ne_zero,addVal_eq_zero_iff.mpr hx,ENat.toNat_zero]
  rfl
lemma value_uniformizer(x:S)(hx:Irreducible x):value S K (algebraMap S K x)=1:=by
  rw [value_integral S K x hx.ne_zero,addVal_def _ 1 hx 1 (by simp),ENat.toNat_one]
  rfl
/-- Integer extraction is used only after explicit finite valuation
identities for the nonzero differential coefficients have been proved. -/
@[expose] def order(x:K):ℤ:=WithTop.untopD 0 (value S K x)
lemma order_eq(x:K)(n:ℤ)(h:value S K x=(n:WithTop ℤ)):order S K x=n:=by
  rw [order,h,WithTop.untopD_coe]
end ActualDvrMeromorphicOrder318

namespace ActualPrimeMeromorphicOrder318
variable (R:Type*) [CommRing R] [IsDomain R] (p:Ideal R) [p.IsPrime]
abbrev Stalk:=Localization.AtPrime p
abbrev F:=FractionRing R
@[expose] def embedding:Stalk R p→+*F R:=
  IsLocalization.lift (fun x:p.primeCompl=>IsUnit.mk0 (algebraMap R (F R) x.val)
    ((map_ne_zero_iff _ (IsFractionRing.injective R (F R))).mpr
      (nonZeroDivisors.ne_zero (p.primeCompl_le_nonZeroDivisors x.property))))
local instance stalkAlgebra:Algebra (Stalk R p) (F R):=(embedding R p).toAlgebra
local instance sourceTower:IsScalarTower R (Stalk R p) (F R):=
  IsScalarTower.of_algebraMap_eq (fun x=>(IsLocalization.lift_eq _ x).symm)
local instance stalkFraction:IsFractionRing (Stalk R p) (F R):=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl (Stalk R p) (F R)
variable [IsDiscreteValuationRing (Stalk R p)]
@[expose] def value:AddValuation (F R) (WithTop ℤ):=
  ActualDvrMeromorphicOrder318.value (Stalk R p) (F R)
@[expose] def order(x:F R):ℤ:=WithTop.untopD 0 (value R p x)
lemma order_eq(x:F R)(n:ℤ)(h:value R p x=(n:WithTop ℤ)):order R p x=n:=by
  rw [order,h,WithTop.untopD_coe]
lemma on_source(x:R):embedding R p (algebraMap R (Stalk R p) x)=algebraMap R (F R) x:=
  IsLocalization.lift_eq _ _
lemma value_source_unit(x:R)(hx:IsUnit (algebraMap R (Stalk R p) x)):
    value R p (algebraMap R (F R) x)=0:=by
  rw [←on_source R p x]
  exact ActualDvrMeromorphicOrder318.value_unit (Stalk R p) (F R) _ hx
lemma value_source_uniformizer(x:R)(hx:Irreducible (algebraMap R (Stalk R p) x)):
    value R p (algebraMap R (F R) x)=1:=by
  rw [←on_source R p x]
  exact ActualDvrMeromorphicOrder318.value_uniformizer (Stalk R p) (F R) _ hx
variable [Algebra ℂ R]
lemma value_two:value R p (2:F R)=0:=by
  have hu:IsUnit (2:Stalk R p):=by
    simpa only [map_ofNat] using (IsUnit.mk0 (2:ℂ) (by norm_num)).map (algebraMap ℂ (Stalk R p))
  simpa only [map_ofNat] using value_source_unit R p (2:R) hu
end ActualPrimeMeromorphicOrder318
