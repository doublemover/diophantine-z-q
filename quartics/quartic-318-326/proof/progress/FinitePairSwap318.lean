module
public import FiniteSymmetryPolynomial318
public import FinitePairCover318
public section
noncomputable section
namespace FinitePairSwap318
open InfinityAdditionAlgebra318
open RelativeChordAlgebra318 (PairRing leftPair rightPair)
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R]
@[expose] def swap (A B:R) : PairRing A B →ₐ[R] PairRing A B :=
  (Algebra.TensorProduct.comm R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).toAlgHom
@[simp] lemma swap_left (A B:R) (x:ShortAffineJacobian318.Ring A B) :
    swap A B (leftPair A B x)=rightPair A B x := by
  simp [swap,leftPair,rightPair,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.comm_tmul]
@[simp] lemma swap_right (A B:R) (x:ShortAffineJacobian318.Ring A B) :
    swap A B (rightPair A B x)=leftPair A B x := by
  simp [swap,leftPair,rightPair,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.comm_tmul]
@[simp] lemma swap_X1 (A B:R) : swap A B (X1 A B)=X2 A B := swap_left A B _
@[simp] lemma swap_Y1 (A B:R) : swap A B (Y1 A B)=Y2 A B := swap_left A B _
@[simp] lemma swap_X2 (A B:R) : swap A B (X2 A B)=X1 A B := swap_right A B _
@[simp] lemma swap_Y2 (A B:R) : swap A B (Y2 A B)=Y1 A B := swap_right A B _
lemma swap_coeff (A B r:R) : swap A B (coeffMap A B r)=coeffMap A B r := by
  exact (swap A B).commutes r
lemma swap_pow (A B:R) (r:PairRing A B) (n:ℕ) : swap A B (r^n)=(swap A B r)^n :=
  (swap A B).toRingHom.map_pow r n
lemma secant (A B:R) (tangent:Bool) :
    slopeNumerator A B tangent*(X2 A B-X1 A B)=denominator A B tangent*(Y2 A B-Y1 A B) := by
  cases tangent
  · simp only [slopeNumerator,denominator,Bool.false_eq_true,ite_false]
    ring
  · exact FiniteSymmetryPolynomial318.tangent_secant (coeffMap A B A) (coeffMap A B B)
      (X1 A B) (Y1 A B) (X2 A B) (Y2 A B) (first_equation A B) (second_equation A B)
lemma denominator_false (A B:R) : swap A B (denominator A B false)= -denominator A B false := by
  simp only [denominator,Bool.false_eq_true,ite_false,map_sub,swap_X1,swap_X2]
  ring
lemma denominator_true (A B:R) : swap A B (denominator A B true)=denominator A B true := by
  simp only [denominator,ite_true,map_add,swap_Y1,swap_Y2]
  ring
lemma slopeNumerator_false (A B:R) : swap A B (slopeNumerator A B false)= -slopeNumerator A B false := by
  simp only [slopeNumerator,Bool.false_eq_true,ite_false,map_sub,swap_Y1,swap_Y2]
  ring
lemma slopeNumerator_true (A B:R) : swap A B (slopeNumerator A B true)=slopeNumerator A B true := by
  simp only [slopeNumerator,ite_true,map_add,map_mul,swap_pow,swap_X1,swap_X2,swap_coeff]
  ring
lemma numeratorX_swap (A B:R) (tangent:Bool) : swap A B (numeratorX A B tangent)=numeratorX A B tangent := by
  cases tangent
  · simp only [numeratorX,map_sub,map_mul,map_add,swap_pow,swap_X1,swap_X2,
      slopeNumerator_false,denominator_false]
    ring
  · simp only [numeratorX,map_sub,map_mul,map_add,swap_pow,swap_X1,swap_X2,
      slopeNumerator_true,denominator_true]
    ring
lemma numeratorY_false (A B:R) : swap A B (numeratorY A B false)= -numeratorY A B false := by
  simp only [numeratorY,numeratorX,map_sub,map_mul,map_add,swap_pow,swap_X1,swap_X2,swap_Y1,
    slopeNumerator_false,denominator_false]
  exact FiniteSymmetryPolynomial318.reversed_Y (X1 A B) (Y1 A B) (X2 A B) (Y2 A B)
    (denominator A B false) (slopeNumerator A B false) (secant A B false)
lemma numeratorY_true (A B:R) : swap A B (numeratorY A B true)=numeratorY A B true := by
  simp only [numeratorY,numeratorX,map_sub,map_mul,map_add,swap_pow,swap_X1,swap_X2,swap_Y1,
    slopeNumerator_true,denominator_true]
  exact FiniteSymmetryPolynomial318.symmetric_Y (X1 A B) (Y1 A B) (X2 A B) (Y2 A B)
    (denominator A B true) (slopeNumerator A B true) (secant A B true)

/-- The four actual finite-input addition opens are preserved by exchange of the inputs. -/
lemma chartElement_unit {S:Type u} [CommRing S] [Algebra R S]
    (A B:R) (f:PairRing A B →ₐ[R] S) (i:Fin 4)
    (h:IsUnit (f (FinitePairCover318.chartElement A B i))) :
    IsUnit (f (swap A B (FinitePairCover318.chartElement A B i))) := by
  fin_cases i
  · change IsUnit (f (swap A B (denominator A B false)))
    rw [denominator_false,map_neg]
    exact h.neg
  · change IsUnit (f (swap A B (denominator A B true)))
    rw [denominator_true]
    exact h
  · change IsUnit (f (swap A B (numeratorY A B false)))
    rw [numeratorY_false,map_neg]
    exact h.neg
  · change IsUnit (f (swap A B (numeratorY A B true)))
    rw [numeratorY_true]
    exact h
end FinitePairSwap318
