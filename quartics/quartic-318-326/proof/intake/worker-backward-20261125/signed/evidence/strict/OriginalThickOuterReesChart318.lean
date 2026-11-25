module
public import OriginalThickCentralReesChart318
public section
noncomputable section

namespace OriginalThickOuterReesChart318
open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalAffineReesBlowup318 OriginalAffineReesChartLocal318 OriginalReesChartGeneration318
open OriginalReesDomainChart318
open OriginalThickCentralReesChart318 (O x y w I)
open IsLocalization HomogeneousLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable (q : R) (d : ℕ) (ε : Bool) (hq : q ≠ 0)

abbrev C := chart (I q d) (a q d ε) (a_mem q d ε)
abbrev u := chartScalars (I q d) (a q d ε) (a_mem q d ε)
abbrev coefficients : R →+* C q d ε := (u q d ε).comp (algebraMap R (O q d))
local instance : Algebra (O q d) (C q d ε) := (u q d ε).toAlgebra
local instance : Algebra R (C q d ε) := (coefficients q d ε).toAlgebra

abbrev r := u q d ε (a q d ε)
abbrev s := coefficients q d ε q
abbrev ratioOne (z : O q d) (hz : z ∈ I q d) :=
  ratio (I q d) (a q d ε) (a_mem q d ε) 1 ⟨z,by simpa only [pow_one] using hz⟩
abbrev t := ratioOne q d ε (w q d) (OriginalThickCentralReesChart318.hw q d)

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem read (z : O q d) (hz : z ∈ I q d) :
    ratioOne q d ε z hz * r q d ε = u q d ε z := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (generator (I q d) (a q d ε) (a_mem q d ε)))
  have h := congrArg (fun v : C q d ε => v.val)
    (clear_ratio (I q d) (a q d ε) (a_mem q d ε) 1 ⟨z,by simpa only [pow_one] using hz⟩)
  simpa only [val_mul, val_pow, pow_one ((r q d ε).val)] using h

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem abproduct : b q d ε * a q d ε = algebraMap R (O q d) (q^(d+2)) := by
  cases ε
  · change x q d*y q d = _
    rw [mul_comm]
    exact node_relation _
  · exact node_relation _

include hq in
omit [UniqueFactorizationMonoid R] in
theorem a_ne : a q d ε ≠ 0 := by
  exact Bool.casesOn ε (OriginalActualNodeDomain318.axes_nonzero _ (pow_ne_zero _ hq)).2
    (OriginalActualNodeDomain318.axes_nonzero _ (pow_ne_zero _ hq)).1

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem tr : t q d ε * r q d ε = s q d ε := read q d ε _ _

include hq in
theorem b_read : u q d ε (b q d ε) = s q d ε ^ (d+1) * t q d ε := by
  let : IsDomain (O q d) := OriginalActualNodeDomain318.domain _ (pow_ne_zero _ hq)
  let D := Submonoid.powers (generator (I q d) (a q d ε) (a_mem q d ε))
  let F := Localization D
  let j : C q d ε →+* F := algebraMap _ _
  let coeff : R →+* F := j.comp (coefficients q d ε)
  let base : O q d →+* F := j.comp (u q d ε)
  have ht : (t q d ε).val * (r q d ε).val = (s q d ε).val := by
    simpa only [val_mul] using congrArg (fun v : C q d ε => v.val) (tr q d ε)
  apply cancel_scalar_pow (I q d) (a q d ε) (a_mem q d ε) (a_ne q d ε hq) 1
  apply HomogeneousLocalization.val_injective D
  simp only [val_mul, val_pow, pow_one ((r q d ε).val)]
  calc
    (u q d ε (b q d ε)).val * (r q d ε).val
        = base (b q d ε * a q d ε) := (base.map_mul _ _).symm
    _ = coeff (q^(d+2)) := congrArg base (abproduct q d ε)
    _ = (s q d ε).val^(d+2) := coeff.map_pow q (d+2)
    _ = (s q d ε).val^(d+1) * (t q d ε).val * (r q d ε).val := by
      rw [mul_assoc, ht, pow_succ ((s q d ε).val) (d+1)]

include hq in
theorem b_ratio :
    ratioOne q d ε (b q d ε) (b_mem q d ε) = s q d ε ^ d * (t q d ε)^2 := by
  let : IsDomain (O q d) := OriginalActualNodeDomain318.domain _ (pow_ne_zero _ hq)
  let D := Submonoid.powers (generator (I q d) (a q d ε) (a_mem q d ε))
  have ht : (t q d ε).val * (r q d ε).val = (s q d ε).val := by
    simpa only [val_mul] using congrArg (fun v : C q d ε => v.val) (tr q d ε)
  apply cancel_scalar_pow (I q d) (a q d ε) (a_mem q d ε) (a_ne q d ε hq) 1
  apply HomogeneousLocalization.val_injective D
  simp only [val_mul, val_pow, pow_one ((r q d ε).val)]
  calc
    _ = (u q d ε (b q d ε)).val := by
      simpa only [val_mul] using congrArg (fun v : C q d ε => v.val)
        (read q d ε (b q d ε) (b_mem q d ε))
    _ = (s q d ε).val^(d+1) * (t q d ε).val := by
      simpa only [val_mul, val_pow] using congrArg (fun v : C q d ε => v.val) (b_read q d ε hq)
    _ = (s q d ε).val^d * ((t q d ε).val * ((t q d ε).val * (r q d ε).val)) := by
      rw [ht, pow_succ ((s q d ε).val) d]; ac_rfl
    _ = _ := by
      rw [pow_two ((t q d ε).val),
        mul_assoc ((s q d ε).val^d) ((t q d ε).val * (t q d ε).val) ((r q d ε).val),
        mul_assoc ((t q d ε).val) ((t q d ε).val) ((r q d ε).val)]

omit [IsDomain R] [UniqueFactorizationMonoid R] in
/-- Both outer charts are thin, with t=q/a on the actual chart. -/
@[expose] def coordinates : P q →ₐ[R] C q d ε :=
  eval (T := C q d ε) q (r q d ε) (t q d ε) (tr q d ε)

include hq in
theorem chart_base :
    (coordinates q d ε).comp (oldToOuter q d ε) =
      (⟨u q d ε,fun _ => rfl⟩ : O q d →ₐ[R] C q d ε) := by
  have ha : coordinates q d ε (oldToOuter q d ε (a q d ε)) = u q d ε (a q d ε) := by
    rw [old_a,coordinates,eval_x]
  have hb : coordinates q d ε (oldToOuter q d ε (b q d ε)) = u q d ε (b q d ε) := by
    let D := Submonoid.powers (generator (I q d) (a q d ε) (a_mem q d ε))
    let F := Localization D
    let e : C q d ε →+* F := algebraMap _ _
    let cv : P q →+* F := e.comp (coordinates q d ε).toRingHom
    have hq' : cv (algebraMap R (P q) q) = (s q d ε).val :=
      congrArg (fun v : C q d ε => v.val) ((coordinates q d ε).commutes q)
    have hy' : cv (yAxis q) = (t q d ε).val :=
      congrArg (fun v : C q d ε => v.val) (eval_y q (r q d ε) (t q d ε) (tr q d ε))
    apply HomogeneousLocalization.val_injective D
    change cv (oldToOuter q d ε (b q d ε)) = (u q d ε (b q d ε)).val
    rw [old_b, cv.map_mul, cv.map_pow, hq', hy']
    simpa only [val_mul, val_pow] using
      (congrArg (fun v : C q d ε => v.val) (b_read q d ε hq)).symm
  cases ε
  · exact OriginalNodeRingMaps318.ext hb ha
  · exact OriginalNodeRingMaps318.ext ha hb

include hq in
theorem surj : Function.Surjective (coordinates q d ε) := by
  let : IsDomain (O q d) := OriginalActualNodeDomain318.domain _ (pow_ne_zero _ hq)
  let f := coordinates q d ε
  let S : Subalgebra (O q d) (C q d ε) :=
    { f.toRingHom.range with algebraMap_mem' := fun z => ⟨oldToOuter q d ε z,
        DFunLike.congr_fun (chart_base q d ε hq) z⟩ }
  have hrs : ratioOne q d ε (a q d ε) (a_mem q d ε) ∈ S := by
    have he : ratioOne q d ε (a q d ε) (a_mem q d ε) = 1 := by
      apply cancel_scalar_pow (I q d) (a q d ε) (a_mem q d ε) (a_ne q d ε hq) 1
      apply HomogeneousLocalization.val_injective (Submonoid.powers (generator (I q d) (a q d ε) (a_mem q d ε)))
      simp only [val_mul, val_pow, val_one, pow_one ((r q d ε).val), one_mul]
      simpa only [val_mul] using congrArg (fun v : C q d ε => v.val)
        (read q d ε (a q d ε) (a_mem q d ε))
    rw [he]
    exact S.one_mem
  have ht : t q d ε ∈ S := ⟨yAxis q,eval_y ..⟩
  have hpow (z : C q d ε) (hz : z ∈ S) (n : ℕ) : z^n ∈ S := by
    let D := Submonoid.powers (generator (I q d) (a q d ε) (a_mem q d ε))
    induction n with
    | zero =>
      have h : z^0 = 1 := by
        apply HomogeneousLocalization.val_injective D
        rw [val_pow, val_one, pow_zero]
      rw [h]
      exact S.one_mem
    | succ n ih =>
      have h : z^(n+1) = z^n * z := by
        apply HomogeneousLocalization.val_injective D
        rw [val_pow, val_mul, val_pow, pow_succ z.val n]
      rw [h]
      exact S.mul_mem ih hz
  have hbs : ratioOne q d ε (b q d ε) (b_mem q d ε) ∈ S := by
    rw [b_ratio q d ε hq]
    exact S.mul_mem (hpow (s q d ε) (S.algebraMap_mem (w q d)) d) (hpow (t q d ε) ht 2)
  have hset : ({x q d,y q d,w q d} : Set (O q d)) = {a q d ε,b q d ε,w q d} := by
    cases ε
    · change insert (x q d) (insert (y q d) ({w q d} : Set (O q d))) =
        insert (y q d) (insert (x q d) {w q d})
      exact Set.insert_comm ..
    · rfl
  have hs : Algebra.adjoin (O q d)
        {z : C q d ε | ∃ v : ↥((I q d)^1),
          v.val ∈ ({x q d,y q d,w q d} : Set (O q d)) ∧
            ratio (I q d) (a q d ε) (a_mem q d ε) 1 v = z} ≤ S := by
    apply Algebra.adjoin_le
    rintro z ⟨⟨v,hv⟩,hh,rfl⟩
    rw [hset] at hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl | rfl
    · exact hrs
    · exact hbs
    · exact ht
  rw [generated _ _ _ (a_ne q d ε hq) _ rfl] at hs
  intro z
  exact hs (show z ∈ (⊤ : Subalgebra (O q d) (C q d ε)) from trivial)

end OriginalThickOuterReesChart318

#print axioms OriginalThickOuterReesChart318.coordinates
#print axioms OriginalThickOuterReesChart318.chart_base
#print axioms OriginalThickOuterReesChart318.surj
