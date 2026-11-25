module
public import OriginalThickCentralReesChart318
public section
noncomputable section

namespace OriginalThickCentralReesIso318

open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalAffineReesBlowup318 OriginalAffineReesChartLocal318 OriginalReesDomainChart318
open OriginalThickCentralReesChart318
open IsLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable (q : R) (d : ℕ) (hq : q ≠ 0)

abbrev w' := algebraMap R (P q d) q
abbrev Q := Localization.Away (w' q d)
abbrev j := Algebra.algHom R (P q d) (Q q d)
abbrev f := (j q d).toRingHom.comp (oldToNew q d).toRingHom
local instance : Algebra R (B q d) := ((bas q d).comp (algebraMap R (O q d))).toAlgebra

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem denom_unit : IsUnit (f q d (w q d)) := by
  change IsUnit (j q d (oldToNew q d (algebraMap R (O q d) q)))
  rw [AlgHom.commutes]
  exact Away.algebraMap_isUnit (w' q d)

omit [IsDomain R] [UniqueFactorizationMonoid R] in
@[expose] def localRead : B q d →ₐ[R] Q q d := by
  let F : Localization.Away (w q d) →+* Q q d :=
    Away.lift (g:=f q d) (w q d) (denom_unit q d)
  refine ⟨F.comp (chartEval (I q d) (w q d) (hw q d)), fun z => ?_⟩
  change Away.lift (w q d) (denom_unit q d)
    (chartEval (I q d) (w q d) (hw q d) (bas q d (algebraMap R (O q d) z))) = _
  rw [chartEval_scalar,Away.lift_eq]
  change j q d (oldToNew q d (algebraMap R (O q d) z)) = _
  rw [AlgHom.commutes,AlgHom.commutes]

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem localRead_on_old (z : O q d) :
    localRead q d (bas q d z) = j q d (oldToNew q d z) := by
  change Away.lift (w q d) (denom_unit q d)
    (chartEval (I q d) (w q d) (hw q d) (bas q d z)) = _
  rw [chartEval_scalar,Away.lift_eq]
  rfl

include hq in
theorem composition :
    (localRead q d).comp (coordinates q d hq) = j q d := by
  have hw : oldToNew q d (w q d) = w' q d := (oldToNew q d).commutes q
  have hun : IsUnit (j q d (w' q d)) := Away.algebraMap_isUnit _
  have hx : oldToNew q d (x q d) = w' q d * xAxis (q^d) := eval_x ..
  have hy : oldToNew q d (y q d) = w' q d * yAxis (q^d) := eval_y ..
  apply OriginalNodeRingMaps318.ext
  · rw [AlgHom.comp_apply,coordinates,eval_x]
    apply hun.mul_right_cancel
    have h := congrArg (localRead q d) (ratio_read q d (x q d) (Ideal.subset_span (by simp)))
    change localRead q d (u q d * bas q d (w q d)) = localRead q d (bas q d (x q d)) at h
    rw [map_mul,localRead_on_old,localRead_on_old,hw,hx,map_mul,mul_comm (j q d (w' q d))] at h
    exact h
  · rw [AlgHom.comp_apply,coordinates,eval_y]
    apply hun.mul_right_cancel
    have h := congrArg (localRead q d) (ratio_read q d (y q d) (Ideal.subset_span (by simp)))
    change localRead q d (v q d * bas q d (w q d)) = localRead q d (bas q d (y q d)) at h
    rw [map_mul,localRead_on_old,localRead_on_old,hw,hy,map_mul,mul_comm (j q d (w' q d))] at h
    exact h

include hq in
theorem inj : Function.Injective (coordinates q d hq) := by
  let : IsDomain (P q d) := OriginalActualNodeDomain318.domain _ (pow_ne_zero _ hq)
  have H : w' q d ≠ 0 := by
    intro h
    apply hq
    exact (OriginalActualNodeDomain318.scalar_injective (q^d)) (h.trans (map_zero _).symm)
  have hi : Function.Injective (j q d) := base_local_injective _ H
  intro z t h
  apply hi
  rw [← composition q d hq]
  exact congrArg (localRead q d) h

include hq in
/-- The genuine degree-zero q-chart of the original maximal-ideal
Rees algebra is the prescribed thinner node. -/
@[expose] def chartIso : P q d ≃ₐ[R] B q d :=
  AlgEquiv.ofBijective (coordinates q d hq) ⟨inj q d hq,surj q d hq⟩

include hq in
theorem old_reads (z : O q d) :
    chartIso q d hq (oldToNew q d z) = bas q d z :=
  DFunLike.congr_fun (chart_base q d hq) z

end OriginalThickCentralReesIso318

#print axioms OriginalThickCentralReesIso318.chartIso
#print axioms OriginalThickCentralReesIso318.old_reads
