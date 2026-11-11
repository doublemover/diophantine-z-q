module
public import UnitScaleQuadraticZoomEquiv318
public section
noncomputable section
namespace FieldQuadraticZoomEquiv318
open Polynomial
set_option maxHeartbeats 1400000
variable {K : Type*} [Field K] [CharZero K] (α β γ : Fin 4 → K) (t : K)
  (y : Fin 4 → K) (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value α β γ t i)
  (hn : ∀ i,y i≠0)
theorem scale_ne : IntegralQuadraticPointZoom318.scale α β γ t≠0 := by
  apply mul_ne_zero (by norm_num : (4 : K)≠0)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [←hy i]
  exact pow_ne_zero _ (hn i)

/-- A genuine whole-ring equivalence with the actual original source open.
The scale and all original roots become units only here, over the actual
characteristic-zero field. The integral chart did not invert them. -/
@[expose] def equivalence : UnitScaleQuadraticZoomEquiv318.OriginalOpen α β γ ≃+*
    IntegralZoomNeighborhood318.Chart K α β γ t :=
  UnitScaleQuadraticZoomEquiv318.sourceOpenEquiv α β γ t (fun i => Units.mk0 (y i) (hn i)) hy
    (Units.mk0 (IntegralQuadraticPointZoom318.scale α β γ t) (scale_ne α β γ t y hy hn))
    (Units.mk0 2 (by norm_num)) rfl rfl

theorem scalar (r : K) : equivalence α β γ t y hy hn
    (algebraMap K (UnitScaleQuadraticZoomEquiv318.OriginalOpen α β γ) r)=
      algebraMap K (IntegralZoomNeighborhood318.Chart K α β γ t) r :=
  UnitScaleQuadraticZoomEquiv318.sourceOpenEquiv_scalar _ _ _ _ _ _ _ _ _ _ r

theorem root (i : Fin 4) : equivalence α β γ t y hy hn
    (algebraMap _ (UnitScaleQuadraticZoomEquiv318.OriginalOpen α β γ)
      (FourRootOrderSigns318.generator (UnitScaleQuadraticZoomEquiv318.originalCoefficient α β γ) i))=
    IntegralZoomNeighborhood318.oldRoot K α β γ t y i :=
  UnitScaleQuadraticZoomEquiv318.sourceOpenEquiv_root _ _ _ _ _ _ _ _ _ _ i

theorem coordinate : equivalence α β γ t y hy hn
    (algebraMap _ (UnitScaleQuadraticZoomEquiv318.OriginalOpen α β γ)
      (algebraMap K[X] (UnitScaleQuadraticZoomEquiv318.originalOrder α β γ) X))=
    IntegralZoomNeighborhood318.oldCoordinate K α β γ t := by
  rw [equivalence,UnitScaleQuadraticZoomEquiv318.sourceOpenEquiv_polynomial]
  rw [UnitScaleQuadraticZoomEquiv318.coordinateEquiv,
    PolynomialAffineCoordinateEquiv318.equivalence_X]
  rfl

@[expose] def algebraEquivalence : UnitScaleQuadraticZoomEquiv318.OriginalOpen α β γ ≃ₐ[K]
    IntegralZoomNeighborhood318.Chart K α β γ t :=
  { equivalence α β γ t y hy hn with commutes' := scalar α β γ t y hy hn }
end FieldQuadraticZoomEquiv318
