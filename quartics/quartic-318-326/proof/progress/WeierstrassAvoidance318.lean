module
public import TorusChord318
public import Mathlib.Analysis.Complex.Cardinality
public section
noncomputable section
open Set
namespace WeierstrassAvoidance318
set_option maxHeartbeats 0

lemma lattice_countable (L : PeriodPair) : (L.lattice : Set ℂ).Countable :=
  countable_of_Lindelof_of_discrete (X := L.lattice)

lemma value_fiber_countable (L : PeriodPair) (c : ℂ) : {z | L.weierstrassP z=c}.Countable := by
  obtain ⟨w,hw,hc⟩ := WeierstrassSurjective318.exists_value L c
  have hcnt := lattice_countable L
  have h1 : {z : ℂ | w-z ∈ L.lattice}.Countable := hcnt.preimage sub_right_injective
  have h2 : {z : ℂ | -w-z ∈ L.lattice}.Countable := hcnt.preimage sub_right_injective
  apply (hcnt.union (h1.union h2)).mono
  intro z hz
  by_cases hzl : z ∈ L.lattice
  · exact Or.inl hzl
  · right
    have he : L.weierstrassP z=L.weierstrassP w := hz.trans hc.symm
    have hzs := L.derivWeierstrassP_sq z hzl
    have hws := L.derivWeierstrassP_sq w hw
    rw [he] at hzs
    have heq := hzs.trans hws.symm
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ heq with hy | hy
    · left
      exact (WeierstrassPairInjective318.pair_eq_iff_sub_mem L z w hzl hw).mp ⟨he,hy⟩
    · right
      apply (WeierstrassPairInjective318.pair_eq_iff_sub_mem L z (-w) hzl
        (fun h => hw (neg_mem_iff.mp h))).mp
      exact ⟨by simpa using he,by simpa using hy⟩

lemma derivative_zero_countable (L : PeriodPair) : {z | L.derivWeierstrassP z=0}.Countable := by
  have hi : Function.Injective (fun z : ℂ => -z-z) := by
    intro z w he
    linear_combination -he/2
  have hcnt := (lattice_countable L).preimage hi
  apply hcnt.mono
  intro z hz
  change L.derivWeierstrassP z = 0 at hz
  by_cases hzl : z ∈ L.lattice
  · exact sub_mem (neg_mem hzl) hzl
  · apply (WeierstrassPairInjective318.pair_eq_iff_sub_mem L z (-z) hzl
      (fun h => hzl (neg_mem_iff.mp h))).mp
    simp [hz]

/-- An actual auxiliary complex argument avoids every exceptional ordinary-chord condition. -/
theorem exists_auxiliary (L : PeriodPair) (z w : ℂ) :
    ∃ v : ℂ, v ∉ L.lattice ∧ z+v ∉ L.lattice ∧
      L.derivWeierstrassP v≠0 ∧ L.derivWeierstrassP (z+v)≠0 ∧
      L.weierstrassP v≠L.weierstrassP z ∧
      L.weierstrassP v≠L.weierstrassP (z+w) ∧
      L.weierstrassP (z+v)≠L.weierstrassP w := by
  let B : Set ℂ := (L.lattice : Set ℂ) ∪
    ((fun v : ℂ => z+v) ⁻¹' L.lattice) ∪
    {v | L.derivWeierstrassP v=0} ∪
    ((fun v : ℂ => z+v) ⁻¹' {v | L.derivWeierstrassP v=0}) ∪
    {v | L.weierstrassP v=L.weierstrassP z} ∪
    {v | L.weierstrassP v=L.weierstrassP (z+w)} ∪
    ((fun v : ℂ => z+v) ⁻¹' {v | L.weierstrassP v=L.weierstrassP w})
  have hB : B.Countable := ((((((lattice_countable L).union
    ((lattice_countable L).preimage (add_right_injective z))).union
      (derivative_zero_countable L)).union
      ((derivative_zero_countable L).preimage (add_right_injective z))).union
      (value_fiber_countable L (L.weierstrassP z))).union
      (value_fiber_countable L (L.weierstrassP (z+w)))).union
      ((value_fiber_countable L (L.weierstrassP w)).preimage (add_right_injective z))
  have hex : ∃ v : ℂ, v ∉ B := by
    by_contra hh
    push Not at hh
    have hu : B=Set.univ := Set.eq_univ_of_forall hh
    rw [hu] at hB
    exact not_countable_complex hB
  obtain ⟨v,hv⟩ := hex
  refine ⟨v,?_⟩
  simpa only [B,mem_union,mem_preimage,mem_ofPred_eq,SetLike.mem_coe,not_or,and_assoc] using hv
end WeierstrassAvoidance318
