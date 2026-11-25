module
public import OriginalR40ActualOldChartMaps318
public import OriginalActualNodeDomain318
public import OriginalReesChartGeneration318
public section
noncomputable section

namespace OriginalThickCentralReesChart318

open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalAffineReesBlowup318 OriginalAffineReesChartLocal318 OriginalReesDomainChart318
open OriginalReesChartGeneration318
open HomogeneousLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable (q : R) (d : ℕ) (hq : q ≠ 0)

abbrev B := chart (I q d) (w q d) (hw q d)
abbrev bas := chartScalars (I q d) (w q d) (hw q d)
abbrev coefficients : R →+* B q d := (bas q d).comp (algebraMap R (O q d))
local instance : Algebra (O q d) (B q d) := (bas q d).toAlgebra
local instance : Algebra R (B q d) := (coefficients q d).toAlgebra

abbrev ratioOne (a : O q d) (h : a ∈ I q d) :=
  ratio (I q d) (w q d) (hw q d) 1 ⟨a, by simpa only [pow_one] using h⟩
abbrev u := ratioOne q d (x q d) (Ideal.subset_span (by simp))
abbrev v := ratioOne q d (y q d) (Ideal.subset_span (by simp))

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem ratio_read (a : O q d) (h : a ∈ I q d) :
    ratioOne q d a h * bas q d (w q d) = bas q d a := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (generator (I q d) (w q d) (hw q d)))
  have H := congrArg (fun z : B q d => z.val) (clear_ratio (I q d) (w q d) (hw q d) 1
    ⟨a,by simpa only [pow_one] using h⟩)
  simpa only [val_mul, val_pow, pow_one ((bas q d (w q d)).val)] using H

include hq in
omit [UniqueFactorizationMonoid R] in
theorem w_ne : w q d ≠ 0 := by
  intro h
  apply hq
  apply OriginalActualNodeDomain318.scalar_injective (q^(d+2))
  exact h.trans (map_zero (algebraMap R (O q d))).symm

include hq in
theorem central_relation :
    v q d * u q d = coefficients q d (q^d) := by
  let : IsDomain (O q d) := OriginalActualNodeDomain318.domain _ (pow_ne_zero _ hq)
  let A := bas q d
  let D := Submonoid.powers (generator (I q d) (w q d) (hw q d))
  let F := Localization D
  let j : B q d →+* F := algebraMap _ _
  let m : O q d →+* F := j.comp A
  let s : R →+* F := m.comp (algebraMap R (O q d))
  have hu : (u q d).val * s q = m (x q d) := by
    have h := congrArg (fun z : B q d => z.val)
      (ratio_read q d (x q d) (Ideal.subset_span (by simp)))
    change (u q d).val * (bas q d (w q d)).val = (bas q d (x q d)).val
    simpa only [val_mul] using h
  have hv : (v q d).val * s q = m (y q d) := by
    have h := congrArg (fun z : B q d => z.val)
      (ratio_read q d (y q d) (Ideal.subset_span (by simp)))
    change (v q d).val * (bas q d (w q d)).val = (bas q d (y q d)).val
    simpa only [val_mul] using h
  apply cancel_scalar_pow (I q d) (w q d) (hw q d) (w_ne q d hq) 2
  apply HomogeneousLocalization.val_injective D
  simp only [val_mul, val_pow]
  change (v q d).val * (u q d).val * (s q)^2 = s (q^d) * (s q)^2
  calc
    _ = ((v q d).val * s q) * ((u q d).val * s q) := by rw [pow_two]; ac_rfl
    _ = m (y q d * x q d) := by rw [hv,hu,m.map_mul]
    _ = s (q^(d+2)) := congrArg m (node_relation _)
    _ = _ := (congrArg (fun z : R => s z) (pow_add q d 2)).trans
      ((s.map_mul (q^d) (q^2)).trans (congrArg (fun z : F => s (q^d) * z) (s.map_pow q 2)))

include hq in
/-- The coordinates send the central parameters to x/q,y/q in the
honest Rees chart, not to independent regular symbols. -/
@[expose] def coordinates : P q d →ₐ[R] B q d :=
  eval (T := B q d) (q^d) (u q d) (v q d) (central_relation q d hq)

include hq in
theorem chart_base :
    (coordinates q d hq).comp (oldToNew q d) =
      (⟨bas q d,fun _ => rfl⟩ : O q d →ₐ[R] B q d) := by
  apply OriginalNodeRingMaps318.ext
  · rw [AlgHom.comp_apply,oldToNew,eval_x,map_mul,AlgHom.commutes,
      coordinates,eval_x]
    apply HomogeneousLocalization.val_injective (Submonoid.powers (generator (I q d) (w q d) (hw q d)))
    rw [val_mul]
    change (bas q d (w q d)).val * (u q d).val = (bas q d (x q d)).val
    rw [mul_comm]
    simpa only [val_mul] using congrArg (fun z : B q d => z.val)
      (ratio_read q d (x q d) (Ideal.subset_span (by simp)))
  · rw [AlgHom.comp_apply,oldToNew,eval_y,map_mul,AlgHom.commutes,
      coordinates,eval_y]
    apply HomogeneousLocalization.val_injective (Submonoid.powers (generator (I q d) (w q d) (hw q d)))
    rw [val_mul]
    change (bas q d (w q d)).val * (v q d).val = (bas q d (y q d)).val
    rw [mul_comm]
    simpa only [val_mul] using congrArg (fun z : B q d => z.val)
      (ratio_read q d (y q d) (Ideal.subset_span (by simp)))

include hq in
theorem surj : Function.Surjective (coordinates q d hq) := by
  let : IsDomain (O q d) := OriginalActualNodeDomain318.domain _ (pow_ne_zero _ hq)
  let f := coordinates q d hq
  let S : Subalgebra (O q d) (B q d) :=
    { f.toRingHom.range with algebraMap_mem' := fun a => ⟨oldToNew q d a,
        DFunLike.congr_fun (chart_base q d hq) a⟩ }
  have hs : Algebra.adjoin (O q d)
        {z : B q d | ∃ b : ↥((I q d)^1),
          b.val ∈ ({x q d,y q d,w q d} : Set (O q d)) ∧
            ratio (I q d) (w q d) (hw q d) 1 b = z} ≤ S := by
    apply Algebra.adjoin_le
    rintro z ⟨⟨r,hr⟩,ht,rfl⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨xAxis (q^d),eval_x ..⟩
    · exact ⟨yAxis (q^d),eval_y ..⟩
    · have h : ratioOne q d (w q d) (hw q d) = 1 := by
        apply cancel_scalar_pow (I q d) (w q d) (hw q d) (w_ne q d hq) 1
        apply HomogeneousLocalization.val_injective (Submonoid.powers (generator (I q d) (w q d) (hw q d)))
        simp only [val_mul, val_pow, val_one, pow_one ((bas q d (w q d)).val), one_mul]
        simpa only [val_mul] using congrArg (fun z : B q d => z.val)
          (ratio_read q d (w q d) (hw q d))
      change ratioOne q d (w q d) (hw q d) ∈ S
      rw [h]
      exact S.one_mem
  rw [generated _ _ _ (w_ne q d hq) _ rfl] at hs
  intro z
  exact hs (show z ∈ (⊤ : Subalgebra (O q d) (B q d)) from trivial)

end OriginalThickCentralReesChart318

#print axioms OriginalThickCentralReesChart318.coordinates
#print axioms OriginalThickCentralReesChart318.chart_base
#print axioms OriginalThickCentralReesChart318.surj
