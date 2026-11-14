module
public import ActualTwoDescentTorsionSignHom318
public section
noncomputable section
namespace ActualTwoDescentTorsionSignEquivalence318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionKummerValues318
open ActualTwoDescentActualTorsionPoint318 ActualTwoDescentSquareOneUnits318
open ActualTwoDescentTorsionAdditionTable318 ActualTwoDescentTorsionSignValues318 ActualTwoDescentTorsionSignHom318
open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentGaloisTwoTorsion318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_torsion_sign_injective (n : ℚ) (hn : n ≠ 0) : Function.Injective (torsionSignHom n hn) := by
  intro T U h
  have hT : (T.toAdd : Point (algebraMap ℚ Qbar n))+(T.toAdd : Point (algebraMap ℚ Qbar n))=0 := by
    simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using T.toAdd.property
  have hU : (U.toAdd : Point (algebraMap ℚ Qbar n))+(U.toAdd : Point (algebraMap ℚ Qbar n))=0 := by
    simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using U.toAdd.property
  obtain ⟨i,hi⟩ := ActualTwoDescentFinitePointCardinality318.actual_two_torsion_exhaustion _ (rational_parameter_ne n hn) T.toAdd hT
  obtain ⟨j,hj⟩ := ActualTwoDescentFinitePointCardinality318.actual_two_torsion_exhaustion _ (rational_parameter_ne n hn) U.toAdd hU
  apply Subtype.ext
  change (T.toAdd : Point _)=(U.toAdd : Point _)
  change torsionSignValue _ _ T.toAdd=torsionSignValue _ _ U.toAdd at h
  rw [hi,hj] at h ⊢
  fin_cases i <;> fin_cases j
  all_goals first | rfl | skip
  all_goals
    simp only [ActualTwoDescentFinitePointCardinality318.fourTorsion,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      actual_sign_zero,actual_sign_zero_torsion,actual_sign_first_torsion,actual_sign_last_torsion] at h
    have hv := congrArg (fun z : SquareOne Qbar × SquareOne Qbar => (((z.1 : Qbarˣ) : Qbar),((z.2 : Qbarˣ) : Qbar))) h
    norm_num [negativeOne] at hv

lemma actual_torsion_sign_surjective (n : ℚ) (hn : n ≠ 0) : Function.Surjective (torsionSignHom n hn) := by
  rintro ⟨u,v⟩
  rcases actual_square_one_cases u with rfl|rfl <;> rcases actual_square_one_cases v with rfl|rfl
  · exact ⟨1,(torsionSignHom n hn).map_one⟩
  · refine ⟨Multiplicative.ofAdd ⟨torsionPoint _ (rational_parameter_ne n hn),?_⟩,?_⟩
    · simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using actual_torsion_double_zero _ (rational_parameter_ne n hn)
    · exact actual_sign_last_torsion _ _
  · refine ⟨Multiplicative.ofAdd ⟨firstTorsion _ (rational_parameter_ne n hn),?_⟩,?_⟩
    · simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using actual_first_torsion_double _ (rational_parameter_ne n hn)
    · exact actual_sign_first_torsion _ _
  · refine ⟨Multiplicative.ofAdd ⟨zeroTorsion _ (rational_parameter_ne n hn),?_⟩,?_⟩
    · simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using actual_zero_torsion_double _ (rational_parameter_ne n hn)
    · exact actual_sign_zero_torsion _ _

def torsionSignEquiv (n : ℚ) (hn : n ≠ 0) : Multiplicative (closedTwoTorsion n) ≃* (SquareOne Qbar × SquareOne Qbar) :=
  MulEquiv.ofBijective (torsionSignHom n hn) ⟨actual_torsion_sign_injective n hn,actual_torsion_sign_surjective n hn⟩

end ActualTwoDescentTorsionSignEquivalence318
