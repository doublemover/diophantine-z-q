module
public import IntegralQuadraticPointZoom318
public import FourSimpleQuadraticEtale318
public import IntegralRootPointMaps318
public import LocalizedKaehlerFrame318
public import Mathlib.RingTheory.RingHom.Smooth
public section
noncomputable section
namespace IntegralZoomNeighborhood318
open Polynomial
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (V : Type*) [CommRing V] (α β γ : Fin 4 → V) (t : V)
abbrev parameters := IntegralQuadraticPointZoom318.coefficient α β γ t
abbrev Chart := FourSimpleQuadraticEtale318.Ring (parameters V α β γ t)
@[expose] def newCoordinate : Chart V α β γ t := algebraMap V[X] (Chart V α β γ t) X
@[expose] def oldCoordinate : Chart V α β γ t :=
  algebraMap V[X] (Chart V α β γ t) (IntegralQuadraticPointZoom318.coordinate α β γ t)
@[expose] def generator (i : Fin 4) : Chart V α β γ t :=
  FourSimpleQuadraticEtale318.generator (parameters V α β γ t) i

theorem etale : Algebra.Etale V[X] (Chart V α β γ t) := FourSimpleQuadraticEtale318.etale _
theorem smooth : Algebra.Smooth V (Chart V α β γ t) := by
  letI : Algebra.Smooth V V[X] := ⟨inferInstance,inferInstance⟩
  letI : Algebra.Etale V[X] (Chart V α β γ t) := etale V α β γ t
  exact Algebra.Smooth.comp V V[X] (Chart V α β γ t)

@[expose] def frame : KaehlerDifferential V (Chart V α β γ t) ≃ₗ[Chart V α β γ t] Chart V α β γ t := by
  letI : Algebra.Etale V[X] (Chart V α β γ t) := etale V α β γ t
  exact LocalizedKaehlerFrame318.etaleFrame (KaehlerDifferential.polynomialEquiv V)

theorem frame_D_oldCoordinate : frame V α β γ t
    (KaehlerDifferential.D V _ (oldCoordinate V α β γ t))=
      algebraMap V (Chart V α β γ t) (IntegralQuadraticPointZoom318.scale α β γ t) := by
  letI : Algebra.Etale V[X] (Chart V α β γ t) := etale V α β γ t
  unfold frame oldCoordinate
  rw [LocalizedKaehlerFrame318.etaleFrame_D,KaehlerDifferential.polynomialEquiv_D]
  simp only [IntegralQuadraticPointZoom318.coordinate,derivative_add,derivative_C,
    derivative_mul,derivative_X,zero_mul,zero_add,mul_one]
  exact (IsScalarTower.algebraMap_apply V V[X] (Chart V α β γ t) _).symm

@[expose] def point : Chart V α β γ t →+* V :=
  FourSimpleQuadraticEtale318.point (parameters V α β γ t) (Polynomial.evalRingHom 0)
    (IntegralQuadraticPointZoom318.coefficient_at_zero α β γ t)

theorem point_polynomial (p : V[X]) : point V α β γ t
    (algebraMap V[X] (Chart V α β γ t) p)=Polynomial.eval 0 p :=
  FourSimpleQuadraticEtale318.point_scalar _ _ _ p
theorem point_generator (i : Fin 4) : point V α β γ t (generator V α β γ t i)=0 :=
  FourSimpleQuadraticEtale318.point_generator _ _ _ i

theorem point_scalar (r : V) : point V α β γ t (algebraMap V (Chart V α β γ t) r)=r := by
  rw [IsScalarTower.algebraMap_apply V V[X] (Chart V α β γ t)]
  change point V α β γ t (algebraMap V[X] (Chart V α β γ t) (C r))=r
  rw [point_polynomial,eval_C]
theorem point_oldCoordinate : point V α β γ t (oldCoordinate V α β γ t)=t := by
  rw [oldCoordinate,point_polynomial]
  simp only [IntegralQuadraticPointZoom318.coordinate,eval_add,eval_C,eval_mul,eval_X,mul_zero,add_zero]

variable (y : Fin 4 → V) (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value α β γ t i)
@[expose] def oldRoot (i : Fin 4) : Chart V α β γ t :=
  algebraMap V (Chart V α β γ t) (y i)*(1+2*generator V α β γ t i)
@[expose] def oldCoefficient (i : Fin 4) : V[X] := C (α i)*X^2+C (β i)*X+C (γ i)
@[expose] def oldScalar : V[X] →+* Chart V α β γ t :=
  Polynomial.eval₂RingHom (algebraMap V (Chart V α β γ t)) (oldCoordinate V α β γ t)

theorem original_root_equation (i : Fin 4) : (oldRoot V α β γ t y i)^2=
    oldScalar V α β γ t (oldCoefficient V α β γ i) := by
  have h := congrArg (algebraMap V[X] (Chart V α β γ t))
    (IntegralQuadraticPointZoom318.transformed_radicand α β γ t i)
  simp only [map_add,map_mul,map_pow,map_one,map_ofNat] at h
  have hC (r : V) : algebraMap V[X] (Chart V α β γ t) (C r)=
      algebraMap V (Chart V α β γ t) r :=
    (IsScalarTower.algebraMap_apply V V[X] (Chart V α β γ t) r).symm
  simp only [hC] at h
  have hg := FourSimpleQuadraticEtale318.generator_relation (parameters V α β γ t) i
  change (generator V α β γ t i)^2+generator V α β γ t i=
    algebraMap V[X] (Chart V α β γ t) (parameters V α β γ t i) at hg
  rw [oldRoot,IntegralQuadraticPointZoom318.root_identity _ _ _ hg,←map_pow,hy i]
  change _=Polynomial.eval₂ (algebraMap V (Chart V α β γ t)) (oldCoordinate V α β γ t)
    (C (α i)*X^2+C (β i)*X+C (γ i))
  simp only [eval₂_add,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X]
  exact h.symm

/-- A map of the ENTIRE actual original four-root order into the smooth
all-prime chart, retaining its original coordinate and every signed root. -/
@[expose] def sourceMap : FourRootOrder318.Order (oldCoefficient V α β γ) →+* Chart V α β γ t := by
  letI : Algebra V[X] (Chart V α β γ t) := (oldScalar V α β γ t).toAlgebra
  exact (IntegralRootPointMaps318.fourMap (oldCoefficient V α β γ)
    (oldRoot V α β γ t y) (original_root_equation V α β γ t y hy)).toRingHom

theorem sourceMap_generator (i : Fin 4) : sourceMap V α β γ t y hy
    (FourRootOrderSigns318.generator (oldCoefficient V α β γ) i)=oldRoot V α β γ t y i := by
  letI : Algebra V[X] (Chart V α β γ t) := (oldScalar V α β γ t).toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator _ _ _ i

theorem point_oldRoot (i : Fin 4) : point V α β γ t (oldRoot V α β γ t y i)=y i := by
  simp only [oldRoot,map_mul,map_add,map_one,map_ofNat,point_scalar,point_generator,mul_zero,add_zero,mul_one]
end IntegralZoomNeighborhood318
