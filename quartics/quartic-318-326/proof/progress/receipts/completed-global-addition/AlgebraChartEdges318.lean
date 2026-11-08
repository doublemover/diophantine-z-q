module
public import AlgebraChartEvaluation318
public section
noncomputable section
namespace AlgebraChartEdges318
open AlgebraicGeometry CategoryTheory
open AlgebraChartEvaluation318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
lemma both_first (A B:R) (f g:I A B →ₐ[R] S) :
    BothInputExtraction318.firstInfinity A B (pair f g)=f := by
  apply AlgHom.ext
  intro r
  exact pair_left f g r
lemma both_second (A B:R) (f g:I A B →ₐ[R] S) :
    BothInputExtraction318.secondInfinity A B (pair f g)=g := by
  apply AlgHom.ext
  intro r
  exact pair_right f g r
lemma both_extract (A B:R) (f g:I A B →ₐ[R] S) (k:F A B →ₐ[R] S)
    (h:infinityInput A B g=finiteInput A B k) :
    BothInputExtraction318.mixedPair A B (pair f g)
      (by simpa only [BothInfinityAlgebra318.V2,BothInfinityAlgebra318.rightPair,pair_right] using transition_unit A B g k h)=
      pair f k := by
  change pair (BothInputExtraction318.firstInfinity A B (pair f g))
    (InfinityExtraction318.finiteMap A B (BothInputExtraction318.secondInfinity A B (pair f g)) _)=_
  simp only [both_first,both_second]
  rw [finiteExtract_eq A B g k h (transition_unit A B g k h)]
lemma both_swap (A B:R) (f g:I A B →ₐ[R] S) :
    (pair f g).comp (BothInputSwap318.swap A B)=pair g f := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro r
    change pair f g (BothInputSwap318.swap A B (BothInfinityAlgebra318.leftPair A B r))=pair g f (BothInfinityAlgebra318.leftPair A B r)
    rw [BothInputSwap318.swap_left]
    exact (pair_right f g r).trans (pair_left g f r).symm
  · apply AlgHom.ext
    intro r
    change pair f g (BothInputSwap318.swap A B (BothInfinityAlgebra318.rightPair A B r))=pair g f (BothInfinityAlgebra318.rightPair A B r)
    rw [BothInputSwap318.swap_right]
    exact (pair_left f g r).trans (pair_right g f r).symm
lemma both_leftExtract (A B:R) (f g:I A B →ₐ[R] S) (k:F A B →ₐ[R] S)
    (h:infinityInput A B f=finiteInput A B k) :
    BothInputSwap318.mixedLeft A B (pair f g)
      (by simpa only [BothInfinityAlgebra318.V1,BothInfinityAlgebra318.leftPair,pair_left] using transition_unit A B f k h)=
      pair g k := by
  unfold BothInputSwap318.mixedLeft
  simpa only [both_swap] using both_extract A B g f k h

theorem both_right_to_mixed (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f g:I A B →ₐ[R] S) (k:F A B →ₐ[R] S) (h:infinityInput A B g=finiteInput A B k) :
    both A B hD f g=mixed A B hD f k := by
  have hv:IsUnit (pair f g (BothInfinityAlgebra318.V2 A B)) := by
    simpa only [BothInfinityAlgebra318.V2,BothInfinityAlgebra318.rightPair,pair_right] using transition_unit A B g k h
  unfold both mixed
  rw [WholeBothNaturality318.right_finite A B hD (pair f g) hv,both_extract A B f g k h]

theorem both_left_to_mixed (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f g:I A B →ₐ[R] S) (k:F A B →ₐ[R] S) (h:infinityInput A B f=finiteInput A B k) :
    both A B hD f g=mixed A B hD g k := by
  have hv:IsUnit (pair f g (BothInfinityAlgebra318.V1 A B)) := by
    simpa only [BothInfinityAlgebra318.V1,BothInfinityAlgebra318.leftPair,pair_left] using transition_unit A B f k h
  unfold both mixed
  rw [WholeBothNaturality318.left_finite A B hD (pair f g) hv,both_leftExtract A B f g k h]

lemma finite_swap (A B:R) (f g:F A B →ₐ[R] S) :
    (pair f g).comp (FinitePairSwap318.swap A B)=pair g f := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro r
    change pair f g (FinitePairSwap318.swap A B (RelativeChordAlgebra318.leftPair A B r))=pair g f (RelativeChordAlgebra318.leftPair A B r)
    rw [FinitePairSwap318.swap_left]
    exact (pair_right f g r).trans (pair_left g f r).symm
  · apply AlgHom.ext
    intro r
    change pair f g (FinitePairSwap318.swap A B (RelativeChordAlgebra318.rightPair A B r))=pair g f (RelativeChordAlgebra318.rightPair A B r)
    rw [FinitePairSwap318.swap_right]
    exact (pair_left f g r).trans (pair_right g f r).symm

theorem finite_comm (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (f g:F A B →ₐ[R] S) :
    finite A B hD f g=finite A B hD g f := by
  have hh:=FiniteAdditionSwapPullback318.equality A B hD (pair f g)
  rw [finite_swap] at hh
  exact hh.symm
end AlgebraChartEdges318
