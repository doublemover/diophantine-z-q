module
public import OriginalAllPrimeGenericComparison318
public section
noncomputable section
namespace OriginalAllPrimeGenericPoint318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPrimeZoomInput318 OriginalAllPrimeGenericComparison318 Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
  {m : Mode} (I : Input c t w D m)
@[expose] def integralEvaluation : I.Chart →ₐ[V c t w] K c t where
  __ := (algebraMap (V c t w) (K c t)).comp I.point
  commutes' r := by
    change algebraMap (V c t w) (K c t) (I.point (algebraMap (V c t w) I.Chart r))=_
    rw [Input.point,IntegralZoomNeighborhood318.point_scalar]
@[expose] def genericEvaluation : GenericChart c t w D I →ₐ[K c t] K c t :=
  Algebra.TensorProduct.lift (AlgHom.id (K c t) (K c t))
    (integralEvaluation c t w D I) (fun _ _ => Commute.all _ _)

theorem genericEvaluation_order (a : I.Chart) : genericEvaluation c t w D I (1 ⊗ₜ[V c t w] a)=
    algebraMap (V c t w) (K c t) (I.point a) := by
  simp [genericEvaluation,Algebra.TensorProduct.lift_tmul,integralEvaluation]

theorem original_signed_root (i : Fin 4) : genericEvaluation c t w D I
    (equivalence c t w D I
      (algebraMap (GenericOrder c t w D (m:=m)) (OriginalOpen c t w D (m:=m))
        (FourRootOrderSigns318.generator (genericCoefficients c t w D (m:=m)) i)))=
      fieldRoot c t w D m i := by
  rw [OriginalAllPrimeGenericComparison318.root,genericEvaluation_order]
  exact I.original_root_value i

theorem original_coordinate : genericEvaluation c t w D I
    (equivalence c t w D I
      (algebraMap (GenericOrder c t w D (m:=m)) (OriginalOpen c t w D (m:=m))
        (algebraMap (K c t)[X] (GenericOrder c t w D (m:=m)) X)))=
      fieldCoordinate c t m := by
  rw [OriginalAllPrimeGenericComparison318.coordinate,genericEvaluation_order]
  rw [Input.point,IntegralZoomNeighborhood318.point_oldCoordinate]
  exact I.coordinate_value

/-- Full generic evaluation induced by the actual integral section,
viewed on the entire original source order. -/
@[expose] def sourceEvaluation : GenericOrder c t w D (m:=m) →+* K c t :=
  ((genericEvaluation c t w D I).toRingHom.comp (equivalence c t w D I).toRingHom).comp
    (algebraMap (GenericOrder c t w D (m:=m)) (OriginalOpen c t w D (m:=m)))

theorem sourceEvaluation_scalar (k : K c t) : sourceEvaluation c t w D I
    (algebraMap (K c t) (GenericOrder c t w D (m:=m)) k)=k := by
  change genericEvaluation c t w D I
    (equivalence c t w D I (algebraMap _ _ (algebraMap _ _ k)))=k
  rw [←IsScalarTower.algebraMap_apply,OriginalAllPrimeGenericComparison318.scalar,AlgHom.commutes]
  rfl

theorem whole_original_point {f : GenericOrder c t w D (m:=m) →+* K c t}
    (hfscalar : ∀ k,f (algebraMap (K c t) (GenericOrder c t w D (m:=m)) k)=k)
    (hfcoordinate : f (algebraMap (K c t)[X] (GenericOrder c t w D (m:=m)) X)=fieldCoordinate c t m)
    (hfroot : ∀ i,f (FourRootOrderSigns318.generator (genericCoefficients c t w D (m:=m)) i)=
      fieldRoot c t w D m i) : sourceEvaluation c t w D I=f := by
  apply IntegralRootPointMaps318.four_ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro k
      change sourceEvaluation c t w D I (algebraMap (K c t) (GenericOrder c t w D (m:=m)) k)=
        f (algebraMap (K c t) (GenericOrder c t w D (m:=m)) k)
      rw [sourceEvaluation_scalar,hfscalar]
    · exact (original_coordinate c t w D I).trans hfcoordinate.symm
  · intro i
    exact (original_signed_root c t w D I i).trans (hfroot i).symm

/-- Both finite and reciprocal modes recover the original, unnormalized
signed root, with its original multiplier and no sign re-selection. -/
theorem recovered_original_root (i : Fin 4) :
    (match m with | .finite => D.multiplier i | .reciprocal => D.multiplier i*(t : K c t))*
      genericEvaluation c t w D I
        (equivalence c t w D I
          (algebraMap (GenericOrder c t w D (m:=m)) (OriginalOpen c t w D (m:=m))
            (FourRootOrderSigns318.generator (genericCoefficients c t w D (m:=m)) i)))=
      roots c t i := by
  rw [original_signed_root]
  cases m with
  | finite =>
    change D.multiplier i*(roots c t i/D.multiplier i)=roots c t i
    field_simp [D.multiplier_ne i]
  | reciprocal =>
    have ht : (t : K c t)≠0 := by
      intro ht
      have h := I.root_value i
      simp only [fieldRoot,ht,mul_zero,div_zero] at h
      exact mapped_root_ne c t w D I i h
    change (D.multiplier i*(t : K c t))*(roots c t i/(D.multiplier i*(t : K c t)))=roots c t i
    field_simp [D.multiplier_ne i,ht]
end OriginalAllPrimeGenericPoint318
