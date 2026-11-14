module
public import OddInfinitySmoothChart318
public import DVRNormalizedInfinityOrder318
public section
noncomputable section
namespace OddInfinityWholeModelMap318
open Polynomial ThreePolynomialEtaleChart318 OddInfinitySmoothChart318
variable (V : Type*) [CommRing V] (pi : V) (u : Fin 4 → Vˣ) (d a : Fin 4 → V)
  (ha : a 0=0) (hd : ∀ i,d i=(u i:V)*pi)
local notation "Q" => OddInfinitySmoothChart318.coefficient V pi u a
local notation "C" => ModelRing V pi u a
@[expose] def z : C := ThreePolynomialEtaleChart318.coordinate V Q
@[expose] def s : C := reciprocalValue V pi u a
@[expose] def ratio (j : Fin 3) : C := ThreeRootCoordinates318.generator _ j
@[expose] def signedRoot : Fin 4 → C :=
  Fin.cases (algebraMap V C pi*z V pi u a)
    (fun j => algebraMap V C pi*z V pi u a*ratio V pi u a j)
@[expose] def scalarMap : V[X] →+* C := Polynomial.eval₂RingHom (algebraMap V C) (s V pi u a)

lemma polynomial_C (v : V) : polynomial V Q (Polynomial.C v)=algebraMap V C v :=
  (IsScalarTower.algebraMap_apply V[X] (Base V Q) C (Polynomial.C v)).symm.trans
    (IsScalarTower.algebraMap_apply V V[X] C v).symm
lemma s_eq : s V pi u a=algebraMap V C (pi*(↑(u 0)⁻¹:V))*(z V pi u a)^2 := by
  have hc := polynomial_C V pi u a (pi*(↑(u 0)⁻¹:V))
  change algebraMap (Base V Q) C (algebraMap V[X] (Base V Q)
    (Polynomial.C (pi*(↑(u 0)⁻¹:V))*X^2))=_
  simp only [map_mul,map_pow]
  rw [hc]
  rfl
lemma ratio_square_polynomial (j : Fin 3) : ratio V pi u a j^2=polynomial V Q (Q j) := by
  fin_cases j <;> simp [ratio,ThreeRootCoordinates318.generator,
    Algebra.TensorProduct.tmul_pow,QuadraticPresentation318.root_square,one_pow,
    Algebra.TensorProduct.algebraMap_def,←AdjoinRoot.algebraMap_eq,FourRootOrderSigns318.scalar_right,
    polynomial]
lemma ratio_square (j : Fin 3) : ratio V pi u a j^2=
    algebraMap V C ((u j.succ:V)*(↑(u 0)⁻¹:V))*(1-algebraMap V C (a j.succ)*s V pi u a) := by
  rw [ratio_square_polynomial]
  simp only [OddInfinitySmoothChart318.coefficient,polynomial,map_mul,map_sub,map_one]
  rw [show algebraMap (Base V Q) C
      (algebraMap V[X] (Base V Q) (Polynomial.C ((u j.succ:V)*(↑(u 0)⁻¹:V))))=_ from
        polynomial_C V pi u a _,
    show algebraMap (Base V Q) C (algebraMap V[X] (Base V Q) (Polynomial.C (a j.succ)))=_ from
      polynomial_C V pi u a _]
  rfl

include ha hd in
lemma signedRoot_square (i : Fin 4) : signedRoot V pi u a i^2=
    scalarMap V pi u a (DVRNormalizedInfinityOrder318.coefficient V d a i) := by
  have hu : algebraMap V C (u 0:V)*algebraMap V C (↑(u 0)⁻¹:V)=1 := by
    rw [←map_mul,Units.mul_inv,map_one]
  refine Fin.cases ?_ (fun j => ?_) i
  · change (algebraMap V C pi*z V pi u a)^2=_
    simp only [scalarMap,DVRNormalizedInfinityOrder318.coefficient,coe_eval₂RingHom,
      eval₂_mul,eval₂_sub,eval₂_C,eval₂_X,eval₂_one,hd,ha,map_zero,zero_mul,sub_zero,mul_one]
    rw [s_eq,map_mul]
    linear_combination -(algebraMap V C pi)^2*(z V pi u a)^2*hu
  · change (algebraMap V C pi*z V pi u a*ratio V pi u a j)^2=_
    rw [mul_pow,ratio_square]
    simp only [scalarMap,DVRNormalizedInfinityOrder318.coefficient,coe_eval₂RingHom,
      eval₂_mul,eval₂_sub,eval₂_C,eval₂_X,eval₂_one,hd,s_eq,map_mul]
    ring

/-- Whole integral reciprocal model map into the PRODUCED smooth odd
infinity chart, including its original coordinate and all signed roots.
Neither pi nor the original center's root coordinate is inverted. -/
@[expose] def sourceMap : DVRNormalizedInfinityOrder318.Order V d a →+* C := by
  letI : Algebra V[X] C := (scalarMap V pi u a).toAlgebra
  exact (IntegralRootPointMaps318.fourMap _ (signedRoot V pi u a)
    (signedRoot_square V pi u d a ha hd)).toRingHom
lemma sourceMap_polynomial (p : V[X]) : sourceMap V pi u d a ha hd
    (algebraMap V[X] (DVRNormalizedInfinityOrder318.Order V d a) p)=scalarMap V pi u a p := by
  letI : Algebra V[X] C := (scalarMap V pi u a).toAlgebra
  exact (IntegralRootPointMaps318.fourMap _ (signedRoot V pi u a)
    (signedRoot_square V pi u d a ha hd)).commutes p
lemma sourceMap_root (i : Fin 4) : sourceMap V pi u d a ha hd
    (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient V d a) i)=
      signedRoot V pi u a i := by
  letI : Algebra V[X] C := (scalarMap V pi u a).toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator _ _ _ i
end OddInfinityWholeModelMap318
