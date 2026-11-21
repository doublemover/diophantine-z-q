module
public import SelectedActualOrdinaryConnected318
public import ActualJOrbitClassification318
public import OpenJComplexEvaluation318
public section
noncomputable section
open scoped MatrixGroups
namespace SelectedActualAdmissiblePeriodPath318

open OpenJComplexEvaluation318

/-- An exact fiber of the ORIGINAL normalized j-function is countable.
Indeed equality of j supplies the actual integral period matrix. No
formal value at either elliptic representative is needed here. -/
theorem countable_j_fiber (a : ℂ) :
    Set.Countable {τ : UpperHalfPlane | ActualQJ318.jInvariant τ = a} := by
  by_cases ha : ∃ τ : UpperHalfPlane, ActualQJ318.jInvariant τ = a
  · obtain ⟨t,ht⟩ := ha
    letI : Countable (SL(2, ℤ)) := by
      change Countable { g : Matrix (Fin 2) (Fin 2) ℤ // Matrix.det g = 1 }
      infer_instance
    refine (Set.countable_range (fun g : SL(2,ℤ) => g • t)).mono ?_
    intro τ hτ
    exact ActualJOrbitClassification318.exists_modular_of_j_eq t τ (ht.trans hτ.symm)
  · have h : {τ : UpperHalfPlane | ActualQJ318.jInvariant τ = a} = ∅ := by
      ext τ
      exact ⟨fun ht => False.elim (ha ⟨τ,ht⟩),False.elim⟩
    rw [h]
    exact Set.countable_empty

/-- Path connectedness of the actual predicate used in the arithmetic
evaluation, not of an abstract punctured cover chosen for the proof. -/
theorem admissible_pathConnected :
    IsPathConnected {τ : UpperHalfPlane | Admissible τ} := by
  let S : Set UpperHalfPlane :=
    {τ | ActualQJ318.jInvariant τ = 0} ∪ {τ | ActualQJ318.jInvariant τ = 1728}
  have hS : {τ : UpperHalfPlane | Admissible τ} = Sᶜ := by
    ext τ
    simp [S,Admissible,not_or]
  rw [hS]
  let e := SelectedActualOrdinaryConnected318.logHeight
  have hr : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  have hcount : S.Countable := (countable_j_fiber 0).union (countable_j_fiber 1728)
  have hpc := (hcount.image e).isPathConnected_compl_of_one_lt_rank hr
  have himg := hpc.image' e.symm.continuous.continuousOn
  have hset : e.symm '' (e '' S)ᶜ = Sᶜ := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩ hz
      exact hw ⟨e.symm w,hz,e.apply_symm_apply w⟩
    · intro hz
      refine ⟨e z, ?_,e.symm_apply_apply z⟩
      rintro ⟨z',hz',he⟩
      exact hz (e.injective he ▸ hz')
  rwa [hset] at himg

end SelectedActualAdmissiblePeriodPath318

#print axioms SelectedActualAdmissiblePeriodPath318.admissible_pathConnected
