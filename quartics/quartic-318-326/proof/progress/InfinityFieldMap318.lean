module
public import InfinityFieldCoordinates318
public import TripleQuadraticField318
public section
noncomputable section
namespace InfinityFieldMap318
open Polynomial QuadraticPresentation318
open scoped TensorProduct
open InfinityFieldCoordinates318
set_option maxHeartbeats 800000
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance originalField : Field (L c):=(KummerTensorField318.source_raw_field c).toField

@[simp] theorem coordinateField_on_polynomial (p:ℚ[X]) :
    coordinateField c (algebraMap ℚ[X] (RatFunc ℚ) p)=Polynomial.aeval (u c) p :=
  RatFunc.liftRingHom_algebraMap _ _ _

theorem parameter_at_coordinate (j:Fin 3) :
    coordinateField c (InfinityParameters318.parameter c j)=ratio c j^2 := by
  rw [InfinityParameters318.parameter,coordinateField_on_polynomial,
    InfinityParameters318.coefficient_shape]
  simp only [map_mul,map_sub,map_pow,Polynomial.aeval_C,Polynomial.aeval_X,map_one]
  exact (ratio_square c j).symm

local instance coordinateAlgebra : Algebra (RatFunc ℚ) (L c) :=
  (coordinateField c).toRingHom.toAlgebra

local instance coordinateSMul : SMul (RatFunc ℚ) (L c) :=
  (coordinateAlgebra c).toSMul
local instance coordinateModule : Module (RatFunc ℚ) (L c) := Algebra.toModule
local instance coordinateSelfTower : IsScalarTower (RatFunc ℚ) (RatFunc ℚ) (L c) where
  smul_assoc a b x := by
    change coordinateField c (a*b)*x=coordinateField c a*(coordinateField c b*x)
    rw [map_mul,mul_assoc]

@[expose] def rootHom (j:Fin 3) :
    RootRing (InfinityParameters318.parameter c j)→ₐ[RatFunc ℚ]L c :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (ratio c j) (by
    change Polynomial.aeval _ (Polynomial.X^2-Polynomial.C (InfinityParameters318.parameter c j))=0
    simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C]
    change ratio c j^2-coordinateField c (InfinityParameters318.parameter c j)=0
    rw [parameter_at_coordinate,sub_self])

@[simp] theorem rootHom_root (j:Fin 3) :
    rootHom c j (AdjoinRoot.root (polynomial (InfinityParameters318.parameter c j)))=ratio c j :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- An actual homomorphism from the degree-eight infinity field to the
original contact field, with base coordinate u and roots y_j/y_0. -/
@[expose] def fieldHom :
    TripleQuadraticField318.Raw (InfinityParameters318.parameter c)→ₐ[RatFunc ℚ]L c :=
  Algebra.TensorProduct.lift (rootHom c 0)
    (Algebra.TensorProduct.lift (rootHom c 1) (rootHom c 2) (fun _ _=>Commute.all _ _))
    (fun _ _=>Commute.all _ _)

theorem fieldHom_injective : Function.Injective (fieldHom c) := by
  letI:Field (TripleQuadraticField318.Raw (InfinityParameters318.parameter c)):=
    (TripleQuadraticField318.infinity_field c).toField
  exact (fieldHom c).injective

/-- The map really transports every rational function in the infinity
coordinate, rather than using the original t-algebra structure. -/
theorem fieldHom_on_base (f:RatFunc ℚ) :
    fieldHom c (algebraMap (RatFunc ℚ)
      (TripleQuadraticField318.Raw (InfinityParameters318.parameter c)) f)=coordinateField c f :=
  (fieldHom c).commutes f
end InfinityFieldMap318
