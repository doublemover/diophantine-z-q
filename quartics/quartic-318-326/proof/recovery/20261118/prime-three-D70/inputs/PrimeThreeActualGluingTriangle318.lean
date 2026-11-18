module
public import PrimeThreeUnchangedVWOverlap318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace PrimeThreeActualGluingTriangle318
open AlgebraicGeometry CategoryTheory
open PrimeThreeSecondFirstOverlapBridges318 PrimeThreeSecondOverlapCocycle318
open PrimeThreeSecondOverlapIntersection318 PrimeThreeUnchangedVWOverlap318

/-- Replace only the actual first-U piece; the other first charts stay unchanged. -/
@[expose] def piece : Fin 3 → Scheme :=
  ![PrimeThreeActualSecondReesProj318.actualSecondProj,
    Spec (CommRingCat.of (FirstOther 0)), Spec (CommRingCat.of (FirstOther 1))]

@[expose] def pair : Fin 3 → Fin 3 → Scheme :=
  ![![piece 0, Spec (CommRingCat.of (FirstOverlap 0)), Spec (CommRingCat.of (FirstOverlap 1))],
    ![Spec (CommRingCat.of (FirstOverlap 0)), piece 1, Spec (CommRingCat.of VWOverlap)],
    ![Spec (CommRingCat.of (FirstOverlap 1)), Spec (CommRingCat.of VWOverlap), piece 2]]

@[expose] def inclusion (i j : Fin 3) (h : i ≠ j) : pair i j ⟶ piece i := by
  fin_cases i <;> fin_cases j
  · exact (h rfl).elim
  · exact overlapToSecond 0
  · exact overlapToSecond 1
  · exact overlapToOther 0
  · exact (h rfl).elim
  · exact vwToV
  · exact overlapToOther 1
  · exact vwToW
  · exact (h rfl).elim

instance inclusion_openImmersion (i j : Fin 3) (h : i ≠ j) : IsOpenImmersion (inclusion i j h) := by
  fin_cases i <;> fin_cases j <;> try exact (h rfl).elim
  all_goals dsimp only [inclusion]; infer_instance

/-- Off-diagonal overlap objects are literally symmetric. -/
@[expose] def transition (i j : Fin 3) (h : i ≠ j) : pair i j ⟶ pair j i := by
  fin_cases i <;> fin_cases j <;> exact 𝟙 _

theorem transition_inverse (i j : Fin 3) (h : i ≠ j) :
    transition i j h ≫ transition j i h.symm = 𝟙 _ := by
  fin_cases i <;> fin_cases j <;> simp only [transition, Category.id_comp]

abbrev Triple := Spec (CommRingCat.of OldTriple)
@[expose] def tripleMap (i j : Fin 3) (h : i ≠ j) : Triple ⟶ pair i j := by
  fin_cases i <;> fin_cases j
  · exact (h rfl).elim
  · exact tripleToVOverlap
  · exact tripleToWOverlap
  · exact tripleToVOverlap
  · exact (h rfl).elim
  · exact tripleToVW
  · exact tripleToWOverlap
  · exact tripleToVW
  · exact (h rfl).elim

theorem triple_transition (i j : Fin 3) (h : i ≠ j) :
    tripleMap i j h ≫ transition i j h = tripleMap j i h.symm := by
  fin_cases i <;> fin_cases j <;> try exact (h rfl).elim
  all_goals simp only [tripleMap, transition, Category.comp_id]

/-- Every ordered distinct triple is the actual common intersection.
The six cases use the three established pullbacks and their flips. -/
theorem ordered_triple_pullback (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    IsPullback (tripleMap i j hij) (tripleMap i k hik) (inclusion i j hij) (inclusion i k hik) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    try exact (hij rfl).elim <;> try exact (hik rfl).elim <;> try exact (hjk rfl).elim
  · exact actual_second_overlap_pullback
  · exact actual_second_overlap_pullback.flip
  · exact actual_V_triple_pullback
  · exact actual_V_triple_pullback.flip
  · exact actual_W_triple_pullback
  · exact actual_W_triple_pullback.flip

@[expose] def pieceToFirst : ∀ i : Fin 3, piece i ⟶ OriginalPrimeThreeNativeReesProj318.actualReesProj
  | 0 => PrimeThreeActualSecondReesProj318.toFirstBlowup
  | 1 => OriginalPrimeThreeNativeReesProj318.nativeChartInclusion 1
  | 2 => OriginalPrimeThreeNativeReesProj318.nativeChartInclusion 2

/-- All three chart morphisms agree on their actual pair overlaps. -/
theorem pieceToFirst_compatible (i j : Fin 3) (h : i ≠ j) :
    inclusion i j h ≫ pieceToFirst i =
      transition i j h ≫ inclusion j i h.symm ≫ pieceToFirst j := by
  fin_cases i <;> fin_cases j <;> try exact (h rfl).elim
  · simpa only [inclusion, transition, pieceToFirst, Category.id_comp] using actual_overlap_span_commutes 0
  · simpa only [inclusion, transition, pieceToFirst, Category.id_comp] using actual_overlap_span_commutes 1
  · simpa only [inclusion, transition, pieceToFirst, Category.id_comp] using (actual_overlap_span_commutes 0).symm
  · change vwToV ≫ OriginalPrimeThreeNativeReesProj318.nativeChartInclusion 1 =
      (𝟙 _) ≫ vwToW ≫ OriginalPrimeThreeNativeReesProj318.nativeChartInclusion 2
    rw [Category.id_comp, vwToV_to_first, vwToW_to_first]
  · simpa only [inclusion, transition, pieceToFirst, Category.id_comp] using (actual_overlap_span_commutes 1).symm
  · change vwToW ≫ OriginalPrimeThreeNativeReesProj318.nativeChartInclusion 2 =
      (𝟙 _) ≫ vwToV ≫ OriginalPrimeThreeNativeReesProj318.nativeChartInclusion 1
    rw [Category.id_comp, vwToV_to_first, vwToW_to_first]

end PrimeThreeActualGluingTriangle318
