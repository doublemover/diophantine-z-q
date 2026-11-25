module
public import OriginalThickOuterReesChart318
public section
noncomputable section

namespace OriginalThickOuterReesIso318
open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalAffineReesBlowup318 OriginalAffineReesChartLocal318
open OriginalReesDomainChart318
open OriginalThickCentralReesChart318 (O w I)
open OriginalThickOuterReesChart318 IsLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable (q : R) (d : ℕ) (ε : Bool) (hq : q ≠ 0)

abbrev Q := Localization.Away (xAxis q)
abbrev j := Algebra.algHom R (P q) (Q q)
abbrev f := (j q).toRingHom.comp (oldToOuter q d ε).toRingHom
local instance : Algebra R (C q d ε) := ((u q d ε).comp (algebraMap R (O q d))).toAlgebra

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem denom_unit : IsUnit (f q d ε (a q d ε)) := by
  change IsUnit (j q (oldToOuter q d ε (a q d ε)))
  rw [old_a]
  exact Away.algebraMap_isUnit (xAxis q)

omit [IsDomain R] [UniqueFactorizationMonoid R] in
@[expose] def localRead : C q d ε →ₐ[R] Q q := by
  let F : Localization.Away (a q d ε) →+* Q q :=
    Away.lift (g:=f q d ε) (a q d ε) (denom_unit q d ε)
  refine ⟨F.comp (chartEval (I q d) (a q d ε) (a_mem q d ε)), fun z => ?_⟩
  change Away.lift (a q d ε) (denom_unit q d ε)
    (chartEval (I q d) (a q d ε) (a_mem q d ε)
      (u q d ε (algebraMap R (O q d) z))) = _
  rw [chartEval_scalar,Away.lift_eq]
  change j q (oldToOuter q d ε (algebraMap R (O q d) z)) = _
  rw [AlgHom.commutes,AlgHom.commutes]

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem localRead_on_old (z : O q d) :
    localRead q d ε (u q d ε z) = j q (oldToOuter q d ε z) := by
  change Away.lift (a q d ε) (denom_unit q d ε)
    (chartEval (I q d) (a q d ε) (a_mem q d ε) (u q d ε z)) = _
  rw [chartEval_scalar,Away.lift_eq]
  rfl

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem composition :
    (localRead q d ε).comp (coordinates q d ε) = j q := by
  have hun : IsUnit (j q (xAxis q)) := Away.algebraMap_isUnit _
  apply OriginalNodeRingMaps318.ext
  · rw [AlgHom.comp_apply,coordinates,eval_x]
    exact (localRead_on_old q d ε _).trans (congrArg (j q) (old_a q d ε))
  · rw [AlgHom.comp_apply,coordinates,eval_y]
    apply hun.mul_right_cancel
    have h := congrArg (localRead q d ε)
      (read q d ε (w q d) (OriginalThickCentralReesChart318.hw q d))
    change localRead q d ε (t q d ε * u q d ε (a q d ε)) =
      localRead q d ε (u q d ε (w q d)) at h
    rw [map_mul,localRead_on_old,old_a,localRead_on_old] at h
    have hq' : oldToOuter q d ε (w q d) = algebraMap R (P q) q :=
      (oldToOuter q d ε).commutes q
    rw [hq',← node_relation, map_mul] at h
    exact h

include hq in
theorem inj : Function.Injective (coordinates q d ε) := by
  let : IsDomain (P q) := OriginalActualNodeDomain318.domain q hq
  have ha := (OriginalActualNodeDomain318.axes_nonzero q hq).1
  have hb : Function.Injective (j q) := OriginalReesDomainChart318.base_local_injective _ ha
  intro v v' h
  apply hb
  rw [← composition q d ε]
  exact congrArg (localRead q d ε) h

include hq in
/-- Either true axial chart of the genuine maximal-ideal Rees blowup
is the thin node uv=q, with the nonchosen old axis read as q^(d+1)v. -/
@[expose] def chartIso : P q ≃ₐ[R] C q d ε :=
  AlgEquiv.ofBijective (coordinates q d ε) ⟨inj q d ε hq,surj q d ε hq⟩

include hq in
theorem old_reads (z : O q d) :
    chartIso q d ε hq (oldToOuter q d ε z) = u q d ε z :=
  DFunLike.congr_fun (chart_base q d ε hq) z

end OriginalThickOuterReesIso318

#print axioms OriginalThickOuterReesIso318.chartIso
#print axioms OriginalThickOuterReesIso318.old_reads
