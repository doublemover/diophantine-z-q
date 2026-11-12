module
public import ActualQuarticOffsetDegree318
public section
noncomputable section
namespace ActualQuarticOffsetZeroLocus318
open TernaryQuadraticLineCover318 IntegerResidueBoxCount318
open OriginalOffsetEliminant318 OriginalOffsetZeroLocus318 OriginalBoundedIntegerShear318
open OriginalControlledIntegralBasis318 ActualAffineQuarticEliminant318
open ActualQuarticOffsetPolynomial318 ActualQuarticOffsetDegree318 ActualOriginalEliminantNonzero318
set_option maxHeartbeats 7000000

@[expose] def ZeroOffsets (κ t : ℤ) (u v d : Vector ℤ) (A B : ℕ) :=
  {a : Interval A×Interval B // actualEliminant κ t (offset u v a.1.1 a.2.1) d=0}

lemma zero_count (κ t : ℤ) (u v d : Vector ℤ) (A B : ℕ)
    (hn : ActualQuarticOffsetPolynomial318.polynomial κ t u v d≠0) :
    Nat.card (ZeroOffsets κ t u v d A B)≤8*((2*A+1)+(2*B+1)) := by
  have hh := grid_zero_count (ActualQuarticOffsetPolynomial318.polynomial κ t u v d) hn 8
    (actual_degree κ t u v d) (Finset.Icc (-(A:ℤ)) A) (Finset.Icc (-(B:ℤ)) B)
    (by rw [interval_card]; omega) (by rw [interval_card]; omega)
  simpa only [GridZeros,ZeroOffsets,Interval,ActualQuarticOffsetPolynomial318.actual_eval,interval_card] using hh

/-- Actual zero-offset cylinders of the TRUE quartic. All 2C+1 remaining
integer points are retained, including t=-2; the same original determinant
constructs polynomial nonvanishing before counting the zero locus. -/
theorem original_zero_cylinder (κ t : ℤ) (hκ : κ≠0) (ht : t≠0)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k)))
    (u v z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ t) κ s u v z)
    (i j : ℤ) (hA : OriginalAffineSieveEliminants318.fA true κ t (shear i j u v z)≠0)
    (A B C : ℕ) :
    Nat.card (ZeroOffsets κ t u v (shear i j u v z) A B × Interval C)≤
      8*((2*A+1)+(2*B+1))*(2*C+1) := by
  have hc := zero_count κ t u v (shear i j u v z) A B
    (actual_original_shear κ t hκ ht s u v z hb i j hA)
  have hI : Nat.card (Interval C)=2*C+1 := by
    simpa only [Nat.card_eq_fintype_card,Interval,Fintype.card_coe] using interval_card C
  rw [Nat.card_prod,hI]
  exact Nat.mul_le_mul_right _ hc

end ActualQuarticOffsetZeroLocus318
