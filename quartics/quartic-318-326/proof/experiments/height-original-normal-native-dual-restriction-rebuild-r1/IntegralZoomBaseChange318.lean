module
public import IntegralZoomNeighborhood318
public import PolynomialQuadraticChartBaseChange318
public section
noncomputable section
namespace IntegralZoomBaseChange318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (α β γ : Fin 4 → R) (t : R)
abbrev mapped (a : Fin 4 → R) := fun i => algebraMap R S (a i)

theorem parameters_map :
    PolynomialQuadraticChartBaseChange318.mapped (S:=S) (IntegralZoomNeighborhood318.parameters R α β γ t)=
      IntegralZoomNeighborhood318.parameters S (mapped (S:=S) α) (mapped (S:=S) β)
        (mapped (S:=S) γ) (algebraMap R S t) := by
  funext i
  simp [PolynomialQuadraticChartBaseChange318.mapped,IntegralZoomNeighborhood318.parameters,
    IntegralQuadraticPointZoom318.coefficient,IntegralQuadraticPointZoom318.cofactor,
    IntegralQuadraticPointZoom318.value,IntegralQuadraticPointZoom318.scale,
    IntegralQuadraticPointZoom318.product,mapped]

@[expose] def parameterEquiv {q q' : Fin 4 → S[X]} (h : q=q') :
    PolynomialQuadraticChartUniversal318.Chart q ≃ₐ[S] PolynomialQuadraticChartUniversal318.Chart q' := by
  subst q'
  exact AlgEquiv.refl

theorem parameterEquiv_coordinate {q q' : Fin 4 → S[X]} (h : q=q') :
    parameterEquiv h (PolynomialQuadraticChartUniversal318.coordinate q)=
      PolynomialQuadraticChartUniversal318.coordinate q' := by subst q'; rfl

theorem parameterEquiv_generator {q q' : Fin 4 → S[X]} (h : q=q') (i : Fin 4) :
    parameterEquiv h (FourSimpleQuadraticEtale318.generator q i)=
      FourSimpleQuadraticEtale318.generator q' i := by subst q'; rfl

@[expose] def equivalence : S ⊗[R] IntegralZoomNeighborhood318.Chart R α β γ t ≃ₐ[S]
    IntegralZoomNeighborhood318.Chart S (mapped (S:=S) α) (mapped (S:=S) β)
      (mapped (S:=S) γ) (algebraMap R S t) :=
  (PolynomialQuadraticChartBaseChange318.equivalence (S:=S)
    (IntegralZoomNeighborhood318.parameters R α β γ t)).trans
      (parameterEquiv (parameters_map (S:=S) α β γ t))

theorem equivalence_coordinate : equivalence (S:=S) α β γ t
    (1 ⊗ₜ[R] IntegralZoomNeighborhood318.newCoordinate R α β γ t)=
    IntegralZoomNeighborhood318.newCoordinate S (mapped (S:=S) α) (mapped (S:=S) β)
      (mapped (S:=S) γ) (algebraMap R S t) := by
  rw [equivalence,AlgEquiv.trans_apply,PolynomialQuadraticChartBaseChange318.equivalence_coordinate,
    parameterEquiv_coordinate]

theorem equivalence_generator (i : Fin 4) : equivalence (S:=S) α β γ t
    (1 ⊗ₜ[R] IntegralZoomNeighborhood318.generator R α β γ t i)=
    IntegralZoomNeighborhood318.generator S (mapped (S:=S) α) (mapped (S:=S) β)
      (mapped (S:=S) γ) (algebraMap R S t) i := by
  rw [equivalence,AlgEquiv.trans_apply,PolynomialQuadraticChartBaseChange318.equivalence_generator,
    parameterEquiv_generator]

theorem scale_map : algebraMap R S (IntegralQuadraticPointZoom318.scale α β γ t)=
    IntegralQuadraticPointZoom318.scale (mapped (S:=S) α) (mapped (S:=S) β)
      (mapped (S:=S) γ) (algebraMap R S t) := by
  simp [IntegralQuadraticPointZoom318.scale,IntegralQuadraticPointZoom318.product,
    IntegralQuadraticPointZoom318.value,mapped]

theorem oldCoordinate_expansion : IntegralZoomNeighborhood318.oldCoordinate R α β γ t=
    algebraMap R _ t+algebraMap R _ (IntegralQuadraticPointZoom318.scale α β γ t)*
      IntegralZoomNeighborhood318.newCoordinate R α β γ t := by
  simp only [IntegralZoomNeighborhood318.oldCoordinate,IntegralQuadraticPointZoom318.coordinate,
    map_add,map_mul,IntegralZoomNeighborhood318.newCoordinate]
  rw [←IsScalarTower.algebraMap_apply,←IsScalarTower.algebraMap_apply]

theorem equivalence_oldCoordinate : equivalence (S:=S) α β γ t
    (1 ⊗ₜ[R] IntegralZoomNeighborhood318.oldCoordinate R α β γ t)=
    IntegralZoomNeighborhood318.oldCoordinate S (mapped (S:=S) α) (mapped (S:=S) β)
      (mapped (S:=S) γ) (algebraMap R S t) := by
  change (equivalence (S:=S) α β γ t)
    ((Algebra.TensorProduct.includeRight : IntegralZoomNeighborhood318.Chart R α β γ t →ₐ[R]
      S ⊗[R] IntegralZoomNeighborhood318.Chart R α β γ t)
        (IntegralZoomNeighborhood318.oldCoordinate R α β γ t))=_
  rw [oldCoordinate_expansion,oldCoordinate_expansion]
  simp only [map_add,map_mul,AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply R S (S ⊗[R] IntegralZoomNeighborhood318.Chart R α β γ t) t,
    IsScalarTower.algebraMap_apply R S (S ⊗[R] IntegralZoomNeighborhood318.Chart R α β γ t)
      (IntegralQuadraticPointZoom318.scale α β γ t),AlgEquiv.commutes,AlgEquiv.commutes]
  rw [scale_map]
  change _+_*equivalence (S:=S) α β γ t
    (1 ⊗ₜ[R] IntegralZoomNeighborhood318.newCoordinate R α β γ t)=_
  rw [equivalence_coordinate]

theorem equivalence_oldRoot (y : Fin 4 → R) (i : Fin 4) : equivalence (S:=S) α β γ t
    (1 ⊗ₜ[R] IntegralZoomNeighborhood318.oldRoot R α β γ t y i)=
    IntegralZoomNeighborhood318.oldRoot S (mapped (S:=S) α) (mapped (S:=S) β)
      (mapped (S:=S) γ) (algebraMap R S t) (mapped (S:=S) y) i := by
  change (equivalence (S:=S) α β γ t)
    ((Algebra.TensorProduct.includeRight : IntegralZoomNeighborhood318.Chart R α β γ t →ₐ[R]
      S ⊗[R] IntegralZoomNeighborhood318.Chart R α β γ t)
        (IntegralZoomNeighborhood318.oldRoot R α β γ t y i))=_
  simp only [IntegralZoomNeighborhood318.oldRoot,map_mul,map_add,map_one,map_ofNat,AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply R S (S ⊗[R] IntegralZoomNeighborhood318.Chart R α β γ t),
    AlgEquiv.commutes]
  rw [show (Algebra.TensorProduct.includeRight : IntegralZoomNeighborhood318.Chart R α β γ t →ₐ[R]
    S ⊗[R] IntegralZoomNeighborhood318.Chart R α β γ t)
      (IntegralZoomNeighborhood318.generator R α β γ t i)=
        1 ⊗ₜ[R] IntegralZoomNeighborhood318.generator R α β γ t i from rfl,
    equivalence_generator]
  rfl
end IntegralZoomBaseChange318
