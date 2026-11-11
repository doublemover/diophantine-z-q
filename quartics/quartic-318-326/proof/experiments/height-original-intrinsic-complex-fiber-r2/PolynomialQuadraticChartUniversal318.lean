module
public import FourSimpleQuadraticUniversal318
public import Mathlib.Algebra.Polynomial.AlgebraMap
public section
noncomputable section
namespace PolynomialQuadraticChartUniversal318
open Polynomial FourSimpleQuadraticEtale318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (q : Fin 4 → R[X])
abbrev Chart := Ring q
@[expose] def coordinate : Chart q := algebraMap R[X] (Chart q) X
theorem aeval_coordinate (p : R[X]) : Polynomial.aeval (coordinate q) p=
    algebraMap R[X] (Chart q) p := by
  have he : Polynomial.aeval (coordinate q)=IsScalarTower.toAlgHom R R[X] (Chart q) := by
    apply Polynomial.algHom_ext
    rfl
  exact AlgHom.congr_fun he p

variable (x : S) (z : Fin 4 → S)
  (hz : ∀ i,(z i)^2+z i=Polynomial.aeval x (q i))
  (hd : ∀ i,IsUnit (2*z i+1))
@[expose] def liftRing : Chart q →+* S := by
  letI : Algebra R[X] S := (Polynomial.aeval x).toRingHom.toAlgebra
  exact (FourSimpleQuadraticUniversal318.lift q z hz hd).toRingHom

theorem liftRing_polynomial (f : R[X]) :
    liftRing q x z hz hd (algebraMap R[X] (Chart q) f)=Polynomial.aeval x f := by
  letI : Algebra R[X] S := (Polynomial.aeval x).toRingHom.toAlgebra
  exact (FourSimpleQuadraticUniversal318.lift q z hz hd).commutes f

@[expose] def lift : Chart q →ₐ[R] S where
  __ := liftRing q x z hz hd
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R R[X] (Chart q)]
    change liftRing q x z hz hd (algebraMap R[X] (Chart q) (C r))=_
    rw [liftRing_polynomial,aeval_C]

theorem lift_coordinate : lift q x z hz hd (coordinate q)=x := by
  change liftRing q x z hz hd (algebraMap R[X] (Chart q) X)=x
  rw [liftRing_polynomial,aeval_X]
theorem lift_generator (i : Fin 4) : lift q x z hz hd (generator q i)=z i := by
  letI : Algebra R[X] S := (Polynomial.aeval x).toRingHom.toAlgebra
  exact FourSimpleQuadraticUniversal318.lift_generator _ _ _ _ i

theorem polynomial_image (f : Chart q →ₐ[R] S) (p : R[X]) :
    f (algebraMap R[X] (Chart q) p)=Polynomial.aeval (f (coordinate q)) p := by
  have he : f.comp (IsScalarTower.toAlgHom R R[X] (Chart q))=
      Polynomial.aeval (f (coordinate q)) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply,IsScalarTower.toAlgHom_apply,aeval_X,coordinate]
  exact AlgHom.congr_fun he p

theorem hom_ext {f g : Chart q →ₐ[R] S} (hx : f (coordinate q)=g (coordinate q))
    (hz : ∀ i,f (generator q i)=g (generator q i)) : f=g := by
  letI : Algebra R[X] S := (Polynomial.aeval (f (coordinate q))).toRingHom.toAlgebra
  let fP : Chart q →ₐ[R[X]] S := { f.toRingHom with commutes' := polynomial_image q f }
  let gP : Chart q →ₐ[R[X]] S := { g.toRingHom with commutes' := fun p => by
    change g (algebraMap R[X] (Chart q) p)=Polynomial.aeval (f (coordinate q)) p
    rw [polynomial_image,hx] }
  have he : fP=gP := FourSimpleQuadraticUniversal318.hom_ext q hz
  apply AlgHom.toRingHom_injective
  exact congrArg AlgHom.toRingHom he
end PolynomialQuadraticChartUniversal318
