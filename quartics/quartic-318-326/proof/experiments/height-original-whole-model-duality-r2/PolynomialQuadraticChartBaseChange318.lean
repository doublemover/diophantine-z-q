module
public import PolynomialQuadraticChartUniversal318
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace PolynomialQuadraticChartBaseChange318
open Polynomial PolynomialQuadraticChartUniversal318 FourSimpleQuadraticEtale318
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (q : Fin 4 → R[X])
abbrev mapped := fun i => (q i).map (algebraMap R S)
abbrev Changed := Chart (mapped (S:=S) q)
@[expose] def coefficientMap : Chart q →ₐ[R] Changed (S:=S) q :=
  PolynomialQuadraticChartUniversal318.lift q (coordinate (mapped (S:=S) q))
    (generator (mapped (S:=S) q))
    (fun i => by
      rw [Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R S (Changed (S:=S) q)).symm]
      rw [aeval_coordinate]
      exact generator_relation (mapped (S:=S) q) i)
    (FourSimpleQuadraticUniversal318.derivative_unit _)

theorem coefficientMap_coordinate : coefficientMap (S:=S) q (coordinate q)=
    coordinate (mapped (S:=S) q) := PolynomialQuadraticChartUniversal318.lift_coordinate _ _ _ _ _
theorem coefficientMap_generator (i : Fin 4) : coefficientMap (S:=S) q (generator q i)=
    generator (mapped (S:=S) q) i := PolynomialQuadraticChartUniversal318.lift_generator _ _ _ _ _ i

@[expose] def forward : S ⊗[R] Chart q →ₐ[S] Changed (S:=S) q :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (coefficientMap q) (fun _ _ => Commute.all _ _)
@[expose] def backward : Changed (S:=S) q →ₐ[S] S ⊗[R] Chart q :=
  PolynomialQuadraticChartUniversal318.lift (mapped (S:=S) q)
    (Algebra.TensorProduct.includeRight (coordinate q))
    (fun i => Algebra.TensorProduct.includeRight (generator q i))
    (fun i => by
      rw [←Polynomial.aeval_eq_aeval_map
        (IsScalarTower.algebraMap_eq R S (S ⊗[R] Chart q)).symm]
      rw [Polynomial.aeval_algHom_apply,aeval_coordinate]
      have h := congrArg (Algebra.TensorProduct.includeRight : Chart q →ₐ[R] S ⊗[R] Chart q)
        (generator_relation q i)
      simpa only [map_add,map_pow] using h)
    (fun i => by
      have h := (FourSimpleQuadraticUniversal318.derivative_unit q i).map
        (Algebra.TensorProduct.includeRight : Chart q →ₐ[R] S ⊗[R] Chart q).toRingHom
      simpa only [map_add,map_mul,map_ofNat,map_one] using h)

theorem backward_coordinate : backward (S:=S) q (coordinate (mapped (S:=S) q))=
    Algebra.TensorProduct.includeRight (coordinate q) :=
  PolynomialQuadraticChartUniversal318.lift_coordinate _ _ _ _ _
theorem backward_generator (i : Fin 4) : backward (S:=S) q (generator (mapped (S:=S) q) i)=
    Algebra.TensorProduct.includeRight (generator q i) :=
  PolynomialQuadraticChartUniversal318.lift_generator _ _ _ _ _ i

theorem forward_includeRight (x : Chart q) : forward (S:=S) q (Algebra.TensorProduct.includeRight x)=
    coefficientMap (S:=S) q x := by
  simp [forward,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]

theorem forward_backward : (forward (S:=S) q).comp (backward q)=AlgHom.id S _ := by
  apply PolynomialQuadraticChartUniversal318.hom_ext
  · simp only [AlgHom.comp_apply,backward_coordinate,forward_includeRight,
      coefficientMap_coordinate,AlgHom.id_apply]
  · intro i
    simp only [AlgHom.comp_apply,backward_generator,forward_includeRight,
      coefficientMap_generator,AlgHom.id_apply]

theorem backward_forward : (backward (S:=S) q).comp (forward q)=AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply PolynomialQuadraticChartUniversal318.hom_ext
    · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,forward_includeRight,
        coefficientMap_coordinate,backward_coordinate,AlgHom.id_apply]
    · intro i
      simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,forward_includeRight,
        coefficientMap_generator,backward_generator,AlgHom.id_apply]

/-- Actual scalar extension, with the polynomial coordinate retained.
This avoids replacing the integral chart's generic fiber by an unrelated
ring with the same displayed equations. -/
@[expose] def equivalence : S ⊗[R] Chart q ≃ₐ[S] Chart (mapped (S:=S) q) :=
  AlgEquiv.ofAlgHom (forward q) (backward q) (forward_backward q) (backward_forward q)

theorem equivalence_coordinate : equivalence (S:=S) q (1 ⊗ₜ[R] coordinate q)=
    coordinate (mapped (S:=S) q) := by
  change forward (S:=S) q (Algebra.TensorProduct.includeRight (coordinate q))=_
  rw [forward_includeRight,coefficientMap_coordinate]
theorem equivalence_generator (i : Fin 4) : equivalence (S:=S) q (1 ⊗ₜ[R] generator q i)=
    generator (mapped (S:=S) q) i := by
  change forward (S:=S) q (Algebra.TensorProduct.includeRight (generator q i))=_
  rw [forward_includeRight,coefficientMap_generator]
end PolynomialQuadraticChartBaseChange318
