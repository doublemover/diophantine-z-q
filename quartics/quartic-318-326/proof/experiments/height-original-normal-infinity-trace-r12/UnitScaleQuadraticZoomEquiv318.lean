module
public import QuadraticZoomRootOpen318
public import PolynomialAffineCoordinateEquiv318
public import FourRootCoefficientEquivalence318
public import AwayRingEquivalence318
public import IntegralZoomNeighborhood318
public section
noncomputable section
namespace UnitScaleQuadraticZoomEquiv318
open Polynomial
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (α β γ : Fin 4 → R) (t : R)
  (y : Fin 4 → Rˣ) (hy : ∀ i,(y i : R)^2=IntegralQuadraticPointZoom318.value α β γ t i)
  (d two : Rˣ) (hd : (d : R)=IntegralQuadraticPointZoom318.scale α β γ t)
  (htwo : (two : R)=2)
abbrev q := IntegralQuadraticPointZoom318.coefficient α β γ t
@[expose] def polynomialUnit (u : Rˣ) : R[X]ˣ := Units.map C.toMonoidHom u
abbrev originalCoefficient := IntegralZoomNeighborhood318.oldCoefficient R α β γ
abbrev originalOrder := FourRootOrder318.Order (originalCoefficient α β γ)
@[expose] def originalDenominator : originalOrder α β γ :=
  ∏ i : Fin 4,FourRootOrderSigns318.generator (originalCoefficient α β γ) i
abbrev OriginalOpen := Localization.Away (originalDenominator α β γ)
@[expose] def coordinateEquiv : R[X] ≃ₐ[R] R[X] := PolynomialAffineCoordinateEquiv318.equivalence t d

theorem coefficient_transport (i : Fin 4) :
    coordinateEquiv t d (originalCoefficient α β γ i)=
      QuadraticZoomRootOpen318.coefficient (q α β γ t) (fun i => polynomialUnit (y i)) i := by
  change Polynomial.aeval (C t+C (d : R)*X)
    (C (α i)*X^2+C (β i)*X+C (γ i))=_
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,hd]
  change C (α i)*(IntegralQuadraticPointZoom318.coordinate α β γ t)^2+
    C (β i)*IntegralQuadraticPointZoom318.coordinate α β γ t+C (γ i)=_
  rw [IntegralQuadraticPointZoom318.transformed_radicand]
  change C (IntegralQuadraticPointZoom318.value α β γ t i)*(1+4*q α β γ t i)=
    (C (y i : R))^2*(1+4*q α β γ t i)
  rw [←map_pow,hy i]

@[expose] def orderEquiv : originalOrder α β γ ≃+*
    QuadraticZoomRootOpen318.Old (q α β γ t) (fun i => polynomialUnit (y i)) :=
  FourRootCoefficientEquivalence318.equivalence (coordinateEquiv t d).toRingEquiv
    (originalCoefficient α β γ)
    (QuadraticZoomRootOpen318.coefficient (q α β γ t) (fun i => polynomialUnit (y i)))
    (coefficient_transport α β γ t y hy d hd)

theorem orderEquiv_generator (i : Fin 4) :
    orderEquiv α β γ t y hy d hd (FourRootOrderSigns318.generator (originalCoefficient α β γ) i)=
      FourRootOrderSigns318.generator
        (QuadraticZoomRootOpen318.coefficient (q α β γ t) (fun i => polynomialUnit (y i))) i :=
  FourRootCoefficientEquivalence318.map_generator _ _ _ _ i

theorem denominator_transport : orderEquiv α β γ t y hy d hd (originalDenominator α β γ)=
    QuadraticZoomRootOpen318.denominator (q α β γ t) (fun i => polynomialUnit (y i)) := by
  simp only [originalDenominator,map_prod,orderEquiv_generator,QuadraticZoomRootOpen318.denominator]

@[expose] def sourceOpenEquiv : OriginalOpen α β γ ≃+* IntegralZoomNeighborhood318.Chart R α β γ t :=
  (AwayRingEquivalence318.equivalence (orderEquiv α β γ t y hy d hd)
    (originalDenominator α β γ)
    (QuadraticZoomRootOpen318.denominator (q α β γ t) (fun i => polynomialUnit (y i)))
    (denominator_transport α β γ t y hy d hd)).trans
  (QuadraticZoomRootOpen318.equivalence (q α β γ t) (fun i => polynomialUnit (y i))
    (polynomialUnit two) (by change C (two : R)=2; rw [htwo,map_ofNat])).toRingEquiv

theorem sourceOpenEquiv_root (i : Fin 4) : sourceOpenEquiv α β γ t y hy d two hd htwo
    (algebraMap (originalOrder α β γ) (OriginalOpen α β γ)
      (FourRootOrderSigns318.generator (originalCoefficient α β γ) i))=
    IntegralZoomNeighborhood318.oldRoot R α β γ t (fun i => (y i : R)) i := by
  change QuadraticZoomRootOpen318.forward _ _
    (AwayRingEquivalence318.map _ _ _ _ _)=_
  rw [AwayRingEquivalence318.map_base,orderEquiv_generator]
  rw [QuadraticZoomRootOpen318.forward_oldRoot]
  change algebraMap R[X] _ (C (y i : R))*(1+2*IntegralZoomNeighborhood318.generator R α β γ t i)=_
  rw [←IsScalarTower.algebraMap_apply]
  rfl

theorem sourceOpenEquiv_polynomial (f : R[X]) : sourceOpenEquiv α β γ t y hy d two hd htwo
    (algebraMap (originalOrder α β γ) (OriginalOpen α β γ)
      (algebraMap R[X] (originalOrder α β γ) f))=
    algebraMap R[X] (IntegralZoomNeighborhood318.Chart R α β γ t) (coordinateEquiv t d f) := by
  change QuadraticZoomRootOpen318.forward _ _
    (AwayRingEquivalence318.map _ _ _ _ _)=_
  rw [AwayRingEquivalence318.map_base]
  change QuadraticZoomRootOpen318.forward _ _
    (algebraMap _ _ (FourRootCoefficientEquivalence318.map _ _ _ _ (algebraMap R[X] _ f)))=_
  rw [FourRootCoefficientEquivalence318.map_scalar,←IsScalarTower.algebraMap_apply,AlgHom.commutes]

theorem sourceOpenEquiv_scalar (r : R) : sourceOpenEquiv α β γ t y hy d two hd htwo
    (algebraMap R (OriginalOpen α β γ) r)=
      algebraMap R (IntegralZoomNeighborhood318.Chart R α β γ t) r := by
  rw [IsScalarTower.algebraMap_apply R R[X] (OriginalOpen α β γ)]
  rw [IsScalarTower.algebraMap_apply R[X] (originalOrder α β γ) (OriginalOpen α β γ)]
  rw [sourceOpenEquiv_polynomial]
  change algebraMap R[X] _ (coordinateEquiv t d (C r))=_
  rw [PolynomialAffineCoordinateEquiv318.equivalence_C]
  exact (IsScalarTower.algebraMap_apply R R[X] _ r).symm
end UnitScaleQuadraticZoomEquiv318
