module
public import OriginalAllPrimeZoomInput318
public import IntegralZoomGenericOpen318
public section
noncomputable section
namespace OriginalAllPrimeGenericComparison318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPrimeZoomInput318 Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
  {m : Mode} (I : Input c t w D m)
@[expose] def genericCoefficients : Fin 4 → (K c t)[X] :=
  fun i => (originalCoefficients c t w D m i).map (algebraMap (V c t w) (K c t))
abbrev GenericOrder := FourRootOrder318.Order (genericCoefficients c t w D (m:=m))
@[expose] def genericDenominator : GenericOrder c t w D (m:=m) :=
  ∏ i : Fin 4,FourRootOrderSigns318.generator (genericCoefficients c t w D (m:=m)) i
abbrev OriginalOpen := Localization.Away (genericDenominator c t w D (m:=m))
abbrev GenericChart := (K c t) ⊗[V c t w] I.Chart

theorem coefficient_identity : genericCoefficients c t w D (m:=m)=
    UnitScaleQuadraticZoomEquiv318.originalCoefficient
      (IntegralZoomGenericOpen318.mapped (K:=K c t) (alpha c t w D m))
      (IntegralZoomGenericOpen318.mapped (K:=K c t) (beta c t w D))
      (IntegralZoomGenericOpen318.mapped (K:=K c t) (gamma c t w D m)) := by
  funext i
  rw [genericCoefficients,OriginalAllPrimeZoomInput318.coefficient_identity]
  simp only [IntegralZoomNeighborhood318.oldCoefficient,Polynomial.map_add,
    Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X]
  rfl

@[expose] def orderIdentification : GenericOrder c t w D (m:=m) ≃+*
    UnitScaleQuadraticZoomEquiv318.originalOrder
      (IntegralZoomGenericOpen318.mapped (K:=K c t) (alpha c t w D m))
      (IntegralZoomGenericOpen318.mapped (K:=K c t) (beta c t w D))
      (IntegralZoomGenericOpen318.mapped (K:=K c t) (gamma c t w D m)) :=
  FourRootCoefficientEquivalence318.equivalence (RingEquiv.refl _) _ _
    (fun i => congrFun (coefficient_identity c t w D (m:=m)) i)

theorem denominator_identification : orderIdentification c t w D (m:=m)
    (genericDenominator c t w D (m:=m))=
      UnitScaleQuadraticZoomEquiv318.originalDenominator
        (IntegralZoomGenericOpen318.mapped (K:=K c t) (alpha c t w D m))
        (IntegralZoomGenericOpen318.mapped (K:=K c t) (beta c t w D))
        (IntegralZoomGenericOpen318.mapped (K:=K c t) (gamma c t w D m)) := by
  simp only [genericDenominator,map_prod,orderIdentification,
    FourRootCoefficientEquivalence318.equivalence,FourRootCoefficientEquivalence318.map_generator,
    UnitScaleQuadraticZoomEquiv318.originalDenominator]

theorem mapped_root_ne (i : Fin 4) : algebraMap (V c t w) (K c t) (I.root i)≠0 := by
  simpa only [map_zero] using
    (IsFractionRing.injective (V c t w) (K c t)).ne (I.root_ne i)

/-- Actual original normalized source open, with the exact finite or
reciprocal coefficients from the SAME all-place Data. Its target is the
actual generic fiber of the constructed integral smooth chart. -/
@[expose] def equivalence : OriginalOpen c t w D (m:=m) ≃+* GenericChart c t w D I :=
  (AwayRingEquivalence318.equivalence (orderIdentification c t w D (m:=m))
    (genericDenominator c t w D (m:=m)) _ (denominator_identification c t w D)).trans
      (IntegralZoomGenericOpen318.equivalence (K:=K c t)
        (alpha c t w D m) (beta c t w D) (gamma c t w D m) I.coordinate
        I.root I.root_equation (mapped_root_ne c t w D I)).toRingEquiv

theorem root (i : Fin 4) : equivalence c t w D I
    (algebraMap (GenericOrder c t w D (m:=m)) (OriginalOpen c t w D (m:=m))
      (FourRootOrderSigns318.generator (genericCoefficients c t w D (m:=m)) i))=
    1 ⊗ₜ[V c t w] IntegralZoomNeighborhood318.oldRoot (V c t w)
      (alpha c t w D m) (beta c t w D) (gamma c t w D m) I.coordinate I.root i := by
  change IntegralZoomGenericOpen318.equivalence _ _ _ _ _ _ _
    (AwayRingEquivalence318.map _ _ _ _ _)=_
  rw [AwayRingEquivalence318.map_base]
  change IntegralZoomGenericOpen318.equivalence _ _ _ _ _ _ _
    (algebraMap _ _ (FourRootCoefficientEquivalence318.map _ _ _ _ _))=_
  rw [FourRootCoefficientEquivalence318.map_generator]
  exact IntegralZoomGenericOpen318.root _ _ _ _ _ _ _ i

theorem coordinate : equivalence c t w D I
    (algebraMap (GenericOrder c t w D (m:=m)) (OriginalOpen c t w D (m:=m))
      (algebraMap (K c t)[X] (GenericOrder c t w D (m:=m)) X))=
    1 ⊗ₜ[V c t w] IntegralZoomNeighborhood318.oldCoordinate (V c t w)
      (alpha c t w D m) (beta c t w D) (gamma c t w D m) I.coordinate := by
  change IntegralZoomGenericOpen318.equivalence _ _ _ _ _ _ _
    (AwayRingEquivalence318.map _ _ _ _ _)=_
  rw [AwayRingEquivalence318.map_base]
  change IntegralZoomGenericOpen318.equivalence _ _ _ _ _ _ _
    (algebraMap _ _ (FourRootCoefficientEquivalence318.map _ _ _ _ (algebraMap _ _ X)))=_
  rw [FourRootCoefficientEquivalence318.map_scalar]
  exact IntegralZoomGenericOpen318.coordinate _ _ _ _ _ _ _

theorem scalar (k : K c t) : equivalence c t w D I
    (algebraMap (K c t) (OriginalOpen c t w D (m:=m)) k)=
      algebraMap (K c t) (GenericChart c t w D I) k := by
  rw [IsScalarTower.algebraMap_apply (K c t) (K c t)[X] (OriginalOpen c t w D (m:=m)),
    IsScalarTower.algebraMap_apply (K c t)[X] (GenericOrder c t w D (m:=m)) (OriginalOpen c t w D (m:=m))]
  change IntegralZoomGenericOpen318.equivalence _ _ _ _ _ _ _
    (AwayRingEquivalence318.map _ _ _ _ _)=_
  rw [AwayRingEquivalence318.map_base]
  change IntegralZoomGenericOpen318.equivalence _ _ _ _ _ _ _
    (algebraMap _ _ (FourRootCoefficientEquivalence318.map _ _ _ _ (algebraMap _ _ (C k))))=_
  rw [FourRootCoefficientEquivalence318.map_scalar]
  change IntegralZoomGenericOpen318.equivalence _ _ _ _ _ _ _
    (algebraMap _ _ (algebraMap _ _ (C k)))=_
  rw [←IsScalarTower.algebraMap_apply,←IsScalarTower.algebraMap_apply]
  exact IntegralZoomGenericOpen318.scalar _ _ _ _ _ _ _ k

@[expose] def algebraEquivalence : OriginalOpen c t w D (m:=m) ≃ₐ[K c t] GenericChart c t w D I :=
  { equivalence c t w D I with commutes' := scalar c t w D I }
end OriginalAllPrimeGenericComparison318
