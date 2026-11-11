module
public import IntegralContactZoomCoefficients318
public import IntegralZoomBaseChange318
public section
noncomputable section
namespace IntegralContactZoomBaseChange318
open Polynomial IntegralContactZoomCoefficients318
open scoped TensorProduct
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (d a : Fin 4 → R) (t : R) (m : Mode)
abbrev mapped (x : Fin 4 → R) := fun i => algebraMap R S (x i)
abbrev Changed := Chart (mapped (S:=S) d) (mapped (S:=S) a) (algebraMap R S t) m
abbrev parameters := IntegralZoomNeighborhood318.parameters R (alpha d a m) d (gamma d a m) t

theorem parameters_map : PolynomialQuadraticChartBaseChange318.mapped (S:=S) (parameters d a t m)=
    parameters (mapped (S:=S) d) (mapped (S:=S) a) (algebraMap R S t) m := by
  funext i
  cases m <;> simp [PolynomialQuadraticChartBaseChange318.mapped,parameters,
    IntegralZoomNeighborhood318.parameters,IntegralQuadraticPointZoom318.coefficient,
    IntegralQuadraticPointZoom318.cofactor,IntegralQuadraticPointZoom318.value,
    IntegralQuadraticPointZoom318.scale,IntegralQuadraticPointZoom318.product,alpha,gamma,mapped]

@[expose] def equivalence : S ⊗[R] Chart d a t m ≃ₐ[S] Changed (S:=S) d a t m :=
  (PolynomialQuadraticChartBaseChange318.equivalence (S:=S) (parameters d a t m)).trans
    (IntegralZoomBaseChange318.parameterEquiv (parameters_map (S:=S) d a t m))
@[expose] def coefficientMap : Chart d a t m →ₐ[R] Changed (S:=S) d a t m :=
  ((equivalence (S:=S) d a t m).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

theorem coefficientMap_coordinate : coefficientMap (S:=S) d a t m
    (IntegralZoomNeighborhood318.newCoordinate R (alpha d a m) d (gamma d a m) t)=
    IntegralZoomNeighborhood318.newCoordinate S
      (alpha (mapped (S:=S) d) (mapped (S:=S) a) m) (mapped (S:=S) d)
      (gamma (mapped (S:=S) d) (mapped (S:=S) a) m) (algebraMap R S t) := by
  change equivalence (S:=S) d a t m (1 ⊗ₜ[R] _)=_
  rw [equivalence,AlgEquiv.trans_apply,PolynomialQuadraticChartBaseChange318.equivalence_coordinate,
    IntegralZoomBaseChange318.parameterEquiv_coordinate]

theorem scale_map : algebraMap R S (IntegralQuadraticPointZoom318.scale (alpha d a m) d (gamma d a m) t)=
    IntegralQuadraticPointZoom318.scale
      (alpha (mapped (S:=S) d) (mapped (S:=S) a) m) (mapped (S:=S) d)
      (gamma (mapped (S:=S) d) (mapped (S:=S) a) m) (algebraMap R S t) := by
  cases m <;> simp [IntegralQuadraticPointZoom318.scale,IntegralQuadraticPointZoom318.product,
    IntegralQuadraticPointZoom318.value,alpha,gamma,mapped]

theorem coefficientMap_oldCoordinate : coefficientMap (S:=S) d a t m (oldCoordinate d a t m)=
    oldCoordinate (mapped (S:=S) d) (mapped (S:=S) a) (algebraMap R S t) m := by
  rw [IntegralZoomBaseChange318.oldCoordinate_expansion,IntegralZoomBaseChange318.oldCoordinate_expansion]
  simp only [map_add,map_mul,AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply R S (Changed (S:=S) d a t m) t,
    IsScalarTower.algebraMap_apply R S (Changed (S:=S) d a t m)
      (IntegralQuadraticPointZoom318.scale (alpha d a m) d (gamma d a m) t),scale_map,
    coefficientMap_coordinate]

theorem coefficientMap_contact : coefficientMap (S:=S) d a t m (contactProduct d a t m)=
    contactProduct (mapped (S:=S) d) (mapped (S:=S) a) (algebraMap R S t) m := by
  cases m <;> simp only [contactProduct,contactFactor,map_prod,map_sub,map_mul,map_one,
    coefficientMap_oldCoordinate,AlgHom.commutes,mapped,←IsScalarTower.algebraMap_apply]

variable (y : Fin 4 → R)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) t i)
theorem mapped_root_equation (i : Fin 4) : (mapped (S:=S) y i)^2=
    IntegralQuadraticPointZoom318.value
      (alpha (mapped (S:=S) d) (mapped (S:=S) a) m) (mapped (S:=S) d)
      (gamma (mapped (S:=S) d) (mapped (S:=S) a) m) (algebraMap R S t) i := by
  have h := congrArg (algebraMap R S) (hy i)
  cases m <;> simpa only [IntegralQuadraticPointZoom318.value,alpha,gamma,mapped,
    map_add,map_mul,map_pow,map_zero,map_neg] using h

/-- Naturality is proved from the full cleared identity and actual generic
units. It does not assume that independently chosen inverse-unit records
are definitionally identical after coefficient change. -/
theorem coefficientMap_q0
    (hd : IsUnit (algebraMap S (Changed (S:=S) d a t m) (∏ i : Fin 4,mapped (S:=S) d i)))
    (hP : IsUnit (contactProduct (mapped (S:=S) d) (mapped (S:=S) a) (algebraMap R S t) m)) :
    coefficientMap (S:=S) d a t m (q0 d a t m)=
      q0 (mapped (S:=S) d) (mapped (S:=S) a) (algebraMap R S t) m := by
  have h := congrArg (coefficientMap (S:=S) d a t m) (q0_cleared d a t m y hy)
  simp only [map_mul,map_pow,AlgHom.commutes,coefficientMap_contact] at h
  rw [IsScalarTower.algebraMap_apply R S (Changed (S:=S) d a t m) (∏ i : Fin 4,d i),map_prod,
    IsScalarTower.algebraMap_apply R S (Changed (S:=S) d a t m)
      (IntegralQuadraticPointZoom318.scale (alpha d a m) d (gamma d a m) t),scale_map] at h
  have hh := ZoomBicanonicalCancellation318.cancel_coefficient hd.unit
    (contactProduct (mapped (S:=S) d) (mapped (S:=S) a) (algebraMap R S t) m)
    (coefficientMap (S:=S) d a t m (q0 d a t m))
    (algebraMap S (Changed (S:=S) d a t m) (IntegralQuadraticPointZoom318.scale
      (alpha (mapped (S:=S) d) (mapped (S:=S) a) m) (mapped (S:=S) d)
      (gamma (mapped (S:=S) d) (mapped (S:=S) a) m) (algebraMap R S t)))
    (by simpa only [hd.unit_spec,mapped] using h)
  apply hP.mul_left_cancel
  exact hh.trans (q0_generic_cleared (mapped (S:=S) d) (mapped (S:=S) a)
    (algebraMap R S t) m (mapped (S:=S) y) (mapped_root_equation (S:=S) d a t m y hy) hd).symm
end IntegralContactZoomBaseChange318
