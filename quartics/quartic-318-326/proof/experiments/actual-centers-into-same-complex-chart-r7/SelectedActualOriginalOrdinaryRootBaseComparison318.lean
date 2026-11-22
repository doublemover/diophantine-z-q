module
public import SelectedActualOriginalOrdinaryScalarBaseComparison318
public import SelectedActualComplexOriginalWholeMonicOpening318
import all SelectedActualComplexOriginalWholeMonicOpening318
import all SelectedActualOriginalOrdinaryScalarBaseComparison318

public section
noncomputable section
open scoped Polynomial TensorProduct
open SelectedActualOriginalOrdinaryScalarBaseComparison318
open SelectedActualComplexOriginalWholeMonicOpening318

namespace SelectedActualOriginalOrdinaryRootBaseComparison318

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])

abbrev pQ := p.map (SelectedOriginalRationalOrdinary318.toRational N)
abbrev pC := p.map (SelectedActualComplexOrdinaryScalar318.toComplex N)

private abbrev d := SelectedOriginalRationalOrdinary318.denominator

theorem whole_polynomial_square :
    (pQ N p).map oldBaseToComplex = pC N p := by
  unfold pQ pC
  rw [Polynomial.map_map, whole_scalar_square]

private theorem literal_second_map :
    (↑identifyMappedBase :
      SelectedActualComplexPolynomialOrdinaryBase318.complexPolynomialBase ℚ ℂ d →+* RC).comp
      (ordinaryScalar ℚ ℂ d) = oldBaseToComplex := by
  unfold oldBaseToComplex scalarBase ordinaryScalar baseInclude
  rfl

private theorem mapped_k_polynomial :
    (originalMappedPolynomial ℚ ℂ d (pQ N p)).map identifyMappedBase = pC N p := by
  unfold originalMappedPolynomial
  rw [Polynomial.map_map, literal_second_map, whole_polynomial_square]

/-- Base changing the actual rational monic chart gives the installed
entire complex monic chart of the same literal p, without choosing a root
component. The explicit x=root and all input-polynomial beta rules follow. -/
def compareOrdinaryRoot : ℂ ⊗[ℚ] AdjoinRoot (pQ N p) ≃+* AdjoinRoot (pC N p) :=
  (originalWholeMonicOpening ℚ ℂ d (pQ N p)).trans
    (AdjoinRoot.mapRingEquiv identifyMappedBase
      (originalMappedPolynomial ℚ ℂ d (pQ N p)) (pC N p)
      (by rw [mapped_k_polynomial]))

private theorem map_mk_eq {A B : Type*} [CommRing A] [CommRing B]
    (e : A →+* B) (a : A[X]) (b : B[X]) (h : b ∣ a.map e) (f : A[X]) :
    AdjoinRoot.map e a b h (AdjoinRoot.mk a f) = AdjoinRoot.mk b (f.map e) := by
  let M : A[X] →+* AdjoinRoot b := (AdjoinRoot.map e a b h).comp (AdjoinRoot.mk a)
  let N : A[X] →+* AdjoinRoot b := (AdjoinRoot.mk b).comp (Polynomial.mapRingHom e)
  have hMN : M = N := by
    apply Polynomial.ringHom_ext
    · intro r
      change AdjoinRoot.map e a b h (AdjoinRoot.of a r) =
        AdjoinRoot.mk b ((Polynomial.C r).map e)
      rw [Polynomial.map_C, AdjoinRoot.map_of] <;> rfl
    · change AdjoinRoot.map e a b h (AdjoinRoot.root a) =
        AdjoinRoot.mk b (Polynomial.X.map e)
      rw [Polynomial.map_X, AdjoinRoot.map_root] <;> rfl
  exact DFunLike.congr_fun hMN f

/-- The actual derivative unit on the original monic presentation is
transported to the very same complex ordinary monic presentation. -/
theorem actual_complex_derivative_unit (hd : IsUnit (AdjoinRoot.mk p p.derivative)) :
    IsUnit (AdjoinRoot.mk (pC N p) (pC N p).derivative) := by
  let e := SelectedActualComplexOrdinaryScalar318.toComplex N
  have dv : pC N p ∣ p.map e := dvd_refl _
  have h := hd.map (AdjoinRoot.map e p (pC N p) dv)
  rw [map_mk_eq] at h
  simpa only [pC, e, Polynomial.derivative_map] using h

theorem compareOrdinaryRoot_mk (f : RQ[X]) :
    compareOrdinaryRoot N p ((1 : ℂ) ⊗ₜ[ℚ] AdjoinRoot.mk (pQ N p) f) =
      AdjoinRoot.mk (pC N p) (f.map oldBaseToComplex) := by
  unfold compareOrdinaryRoot
  rw [RingEquiv.trans_apply, originalWholeMonicOpening_mk]
  rw [AdjoinRoot.coe_mapRingEquiv, map_mk_eq, Polynomial.map_map, literal_second_map]

theorem compareOrdinaryRoot_x :
    compareOrdinaryRoot N p ((1 : ℂ) ⊗ₜ[ℚ] AdjoinRoot.root (pQ N p)) =
      AdjoinRoot.root (pC N p) := by
  change compareOrdinaryRoot N p ((1 : ℂ) ⊗ₜ[ℚ] AdjoinRoot.mk (pQ N p) Polynomial.X) =
      AdjoinRoot.mk (pC N p) Polynomial.X
  rw [compareOrdinaryRoot_mk, Polynomial.map_X]

theorem compareOrdinaryRoot_j :
    compareOrdinaryRoot N p ((1 : ℂ) ⊗ₜ[ℚ] AdjoinRoot.of (pQ N p)
      SelectedOriginalRationalOrdinary318.jCoord) =
      AdjoinRoot.of (pC N p) SelectedComplexOrdinaryBase318.jCoord := by
  change compareOrdinaryRoot N p ((1 : ℂ) ⊗ₜ[ℚ] AdjoinRoot.mk (pQ N p)
    (Polynomial.C SelectedOriginalRationalOrdinary318.jCoord)) =
      AdjoinRoot.mk (pC N p) (Polynomial.C SelectedComplexOrdinaryBase318.jCoord)
  rw [compareOrdinaryRoot_mk, Polynomial.map_C, oldBaseToComplex_j]

end SelectedActualOriginalOrdinaryRootBaseComparison318

#print axioms SelectedActualOriginalOrdinaryRootBaseComparison318.whole_polynomial_square
#print axioms SelectedActualOriginalOrdinaryRootBaseComparison318.compareOrdinaryRoot_x
#print axioms SelectedActualOriginalOrdinaryRootBaseComparison318.compareOrdinaryRoot_j
#print axioms SelectedActualOriginalOrdinaryRootBaseComparison318.actual_complex_derivative_unit
