module
public import IntegralValuativeGenericPoint318
public section
noncomputable section
namespace IntegralValuativeOverlapPoint318
open Polynomial IntegralSourceBranches318 IntegralInfinityCommonBase318
open IntegralOverlapChartMaps318 IntegralFullOverlapLocalization318
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V K : Type*) [CommRing V] [IsDomain V] [ValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  (c : Fin 4 → Vˣ) (t : K) (y : Fin 4 → K)
  (hy : ∀ i, (y i)^2=algebraMap V K (c i : V)*(t-algebraMap V K (contacts V i)))
  (ht : ¬IsLocalization.IsInteger V t)
local instance actualSourceAlgebra : Algebra (SourceOrder V c) (Overlap V c) := sourceAlgebra V c
local instance actualSourceLocalization : IsLocalization.Away (sourceQuartic V c) (Overlap V c) :=
  whole_localization V c

include ht in
theorem quartic_unit : IsUnit (IntegralValuativeGenericPoint318.sourceMap V K c t y hy (sourceQuartic V c)) := by
  rw [sourceQuartic,IntegralValuativeGenericPoint318.sourceMap_polynomial]
  simp only [IntegralBranchBicanonical318.quartic,map_prod,map_sub,Polynomial.aeval_X,Polynomial.aeval_C]
  apply IsUnit.prod_univ_iff.mpr
  intro i
  apply isUnit_iff_ne_zero.mpr
  intro h
  exact ht ⟨contacts V i,(sub_eq_zero.mp h).symm⟩

/-- Restrict the ORIGINAL whole field point to the actual complete quartic
intersection. This is a localization lift along the original source map. -/
@[expose] def commonPoint : Overlap V c →+* K :=
  IsLocalization.Away.lift (g := IntegralValuativeGenericPoint318.sourceMap V K c t y hy)
    (sourceQuartic V c) (quartic_unit V K c t y hy ht)

theorem commonPoint_source (a : SourceOrder V c) :
    commonPoint V K c t y hy ht (IntegralOverlapOpenImmersions318.sourceMap V c a)=
      IntegralValuativeGenericPoint318.sourceMap V K c t y hy a :=
  IsLocalization.Away.lift_eq _ (quartic_unit V K c t y hy ht) a

theorem commonPoint_constant (a : V) :
    commonPoint V K c t y hy ht (commonMap V c (algebraMap V (CommonBase V c) a))=algebraMap V K a := by
  have he : commonMap V c (algebraMap V (CommonBase V c) a)=
      IntegralOverlapOpenImmersions318.sourceMap V c (algebraMap V (SourceOrder V c) a) :=
    ((commonMap V c).commutes a).trans ((IntegralOverlapOpenImmersions318.sourceMap V c).commutes a).symm
  rw [he,commonPoint_source,IntegralValuativeGenericPoint318.sourceMap_constant]

theorem commonPoint_root :
    commonPoint V K c t y hy ht (commonMap V c (rootUnit V c : CommonBase V c))=y 0 := by
  rw [←finite_coordinate,IntegralOriginalRootCoordinates318.coordinate_eq_root]
  change commonPoint V K c t y hy ht
    (IntegralOverlapOpenImmersions318.sourceMap V c (IntegralOriginalRootCoordinates318.root V c 0))=y 0
  rw [commonPoint_source,IntegralValuativeGenericPoint318.sourceMap_generator]

theorem commonPoint_root_inverse :
    commonPoint V K c t y hy ht (commonMap V c (↑(rootUnit V c)⁻¹ : CommonBase V c))=(y 0)⁻¹ := by
  have h := map_units_inv ((commonPoint V K c t y hy ht).comp (commonMap V c).toRingHom) (rootUnit V c)
  simpa only [RingHom.comp_apply,commonPoint_root] using h

theorem commonPoint_reciprocal :
    commonPoint V K c t y hy ht (commonMap V c (reciprocalUnit V c : CommonBase V c))=
      algebraMap V K (c 0 : V)/y 0 := by
  simp only [reciprocalUnit,Units.val_mul,Units.coe_map,map_mul]
  rw [commonPoint_constant,commonPoint_root_inverse]
  rfl

theorem commonPoint_infinity_generator (j : Fin 3) :
    commonPoint V K c t y hy ht
      (IntegralOverlapChartMaps318.infinityMap V c (IntegralOverlapRootGenerators318.infinityGenerator V c j))=
      y j.succ/y 0 := by
  rw [IntegralOverlapRootGenerators318.infinityMap_generator,Algebra.smul_def,map_mul,
    IntegralOtherRootCoordinates318.common_other,commonPoint_source,
    IntegralValuativeGenericPoint318.sourceMap_generator]
  change commonPoint V K c t y hy ht
    (commonMap V c (↑(rootUnit V c)⁻¹ : CommonBase V c))*y j.succ=y j.succ/y 0
  rw [commonPoint_root_inverse,div_eq_mul_inv,mul_comm]
end IntegralValuativeOverlapPoint318
