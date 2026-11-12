module
public import ActualTwoDescentOriginalRootEvaluation318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootMaximalIdeal318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentRootCofactorData318 ActualTwoDescentOriginalRootEvaluation318
variable {K : Type*} [Field K] [CharZero K]

/-- The SAME earlier root ideal is exactly the kernel of actual point evaluation. -/
theorem actual_root_ideal_kernel (n : K) (i : Fin 3) :
    rootIdeal n i=RingHom.ker (rootEvaluation n i) := by
  let J := rootIdeal n i
  let q : AffineChart n →+* AffineChart n ⧸ J := Ideal.Quotient.mk J
  have hf : q (rootNumerator n i)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (by
    rw [show J=rootIdeal n i from rfl,actual_root_ideal_generators]
    exact Ideal.subset_span (by simp))
  have hy : q (affineY n)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (by
    rw [show J=rootIdeal n i from rfl,actual_root_ideal_generators]
    exact Ideal.subset_span (by simp))
  have hx : q (affineX n)=q (affineCoefficient n (root n i)) := by
    exact sub_eq_zero.mp (by simpa only [rootNumerator,map_sub] using hf)
  have he : q=(q.comp (affineCoefficient n)).comp (rootEvaluation n i) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · apply RingHom.ext
        intro a
        change q (affineCoefficient n a)=q (affineCoefficient n (rootEvaluation n i (affineCoefficient n a)))
        rw [actual_evaluation_coefficient]
      · change q (affineX n)=q (affineCoefficient n (rootEvaluation n i (affineX n)))
        rw [actual_evaluation_x]
        exact hx
    · change q (affineY n)=q (affineCoefficient n (rootEvaluation n i (affineY n)))
      rw [actual_evaluation_y,map_zero,hy]
  apply le_antisymm
  · rw [actual_root_ideal_generators]
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl|ha
    · exact actual_evaluation_numerator n i
    · have heq := Set.mem_singleton_iff.mp ha
      subst a
      exact actual_evaluation_y n i
  · intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q a=0
    rw [he]
    change q (affineCoefficient n (rootEvaluation n i a))=0
    change rootEvaluation n i a=0 at ha
    rw [ha,map_zero,map_zero]

instance rootIdealPrime (n : K) (i : Fin 3) : (rootIdeal n i).IsPrime := by
  rw [actual_root_ideal_kernel]
  exact RingHom.ker_isPrime _
instance rootIdealMaximal (n : K) (i : Fin 3) : (rootIdeal n i).IsMaximal := by
  rw [actual_root_ideal_kernel]
  exact RingHom.ker_isMaximal_of_surjective _ (actual_evaluation_surjective n i)
end ActualTwoDescentOriginalRootMaximalIdeal318
