module
public import OddTwistDilatationEtale318
public section
noncomputable section
namespace OddTwistDilatationSourceMap318
open Polynomial OddTwistDilatationCoordinates318 OddTwistDilatationEtale318
open scoped TensorProduct
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (pi : V) (u : Vˣ) (a : V) (d b : Fin 3 → V)

@[expose] def originalCoefficient (j : Fin 4) : V[X] :=
  C (Fin.cases ((u : V)*pi) d j)*(X-C (Fin.cases a b j))
abbrev OriginalOrder := FourRootOrder318.Order (originalCoefficient V pi u a d b)
@[expose] def originalRoot : Fin 4 → Chart V pi u a d b :=
  Fin.cases (algebraMap V (Chart V pi u a d b) pi * coordinate V pi u a d b)
    (ThreeRootCoordinates318.generator _)
@[expose] def originalScalar : V[X] →+* Chart V pi u a d b :=
  Polynomial.eval₂RingHom (algebraMap V (Chart V pi u a d b)) (contactValue V pi u a d b)

lemma three_root_square (j : Fin 3) : (ThreeRootCoordinates318.generator
    (fun k => algebraMap V[X] (Base V pi u a d b) (coefficient pi u a d b k)) j)^2 =
    algebraMap (Base V pi u a d b) (Chart V pi u a d b)
      (algebraMap V[X] (Base V pi u a d b) (coefficient pi u a d b j)) := by
  fin_cases j <;> simp [ThreeRootCoordinates318.generator,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Algebra.TensorProduct.tmul_pow,
    QuadraticPresentation318.root_square,one_pow,
    Algebra.TensorProduct.algebraMap_def,←AdjoinRoot.algebraMap_eq,
    FourRootOrderSigns318.scalar_right]

lemma original_root_square (j : Fin 4) :
    (originalRoot V pi u a d b j)^2 =
      originalScalar V pi u a d b (originalCoefficient V pi u a d b j) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · change (algebraMap V (Chart V pi u a d b) pi * coordinate V pi u a d b)^2 = _
    simp only [originalScalar,originalCoefficient,Fin.cases_zero,coe_eval₂RingHom,
      eval₂_mul,eval₂_C,eval₂_sub,eval₂_X]
    rw [contact_square,map_mul]
    have hu : algebraMap V (Chart V pi u a d b) (u : V) *
        algebraMap V (Chart V pi u a d b) (↑u⁻¹ : V) = 1 := by
      rw [←map_mul,Units.mul_inv,map_one]
    rw [map_mul]
    linear_combination -(algebraMap V (Chart V pi u a d b) pi)^2 *
      (coordinate V pi u a d b)^2 * hu
  · change (ThreeRootCoordinates318.generator _ k)^2 = _
    rw [three_root_square]
    simp only [originalScalar,originalCoefficient,Fin.cases_succ,coe_eval₂RingHom,
      eval₂_mul,eval₂_C,eval₂_sub,eval₂_X,coefficient,map_mul,map_sub,scalar_C,contactValue]

/-- The entire original four-root order maps into the produced chart,
including the original polynomial parameter and ALL original root signs.
The only changed distinguished root is exactly pi*Z. No pi is inverted. -/
@[expose] def sourceMap : OriginalOrder V pi u a d b →+* Chart V pi u a d b := by
  letI : Algebra V[X] (Chart V pi u a d b) := (originalScalar V pi u a d b).toAlgebra
  exact (IntegralRootPointMaps318.fourMap (originalCoefficient V pi u a d b)
    (originalRoot V pi u a d b) (original_root_square V pi u a d b)).toRingHom

theorem sourceMap_polynomial (p : V[X]) :
    sourceMap V pi u a d b (algebraMap V[X] (OriginalOrder V pi u a d b) p) =
      originalScalar V pi u a d b p := by
  letI : Algebra V[X] (Chart V pi u a d b) := (originalScalar V pi u a d b).toAlgebra
  exact (IntegralRootPointMaps318.fourMap (originalCoefficient V pi u a d b)
    (originalRoot V pi u a d b) (original_root_square V pi u a d b)).commutes p

theorem sourceMap_signed_root (j : Fin 4) :
    sourceMap V pi u a d b (FourRootOrderSigns318.generator
      (originalCoefficient V pi u a d b) j) = originalRoot V pi u a d b j := by
  letI : Algebra V[X] (Chart V pi u a d b) := (originalScalar V pi u a d b).toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator _ _ _ j
end OddTwistDilatationSourceMap318
