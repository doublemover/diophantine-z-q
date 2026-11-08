module
public import WeierstrassCoefficientMap318
public import FiniteAdditionGluing318
public section
noncomputable section
namespace FinitePairCoefficient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeChordAlgebra318 (PairRing)
open InfinityAdditionAlgebra318
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
local notation "a" => algebraMap R S
@[expose] def pair (A B:R) : PairRing A B →ₐ[R] PairRing (a A) (a B) :=
  Algebra.TensorProduct.lift (R:=R) (S:=R)
    (((RelativeChordAlgebra318.leftPair (a A) (a B)).restrictScalars R).comp (AffineBaseChange318.coefficientMap (S:=S) A B))
    (((RelativeChordAlgebra318.rightPair (a A) (a B)).restrictScalars R).comp (AffineBaseChange318.coefficientMap (S:=S) A B))
    (by intro x y; exact Commute.all (S:=PairRing (a A) (a B)) _ _)
@[simp] theorem pair_left (A B:R) (x:ShortAffineJacobian318.Ring A B) :
    pair (S:=S) A B (RelativeChordAlgebra318.leftPair A B x)=
      RelativeChordAlgebra318.leftPair (a A) (a B) (AffineBaseChange318.coefficientMap (S:=S) A B x) := by
  simp [pair,RelativeChordAlgebra318.leftPair,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul,RelativeChordAlgebra318.leftPair,RelativeChordAlgebra318.rightPair,map_one]
@[simp] theorem pair_right (A B:R) (x:ShortAffineJacobian318.Ring A B) :
    pair (S:=S) A B (RelativeChordAlgebra318.rightPair A B x)=
      RelativeChordAlgebra318.rightPair (a A) (a B) (AffineBaseChange318.coefficientMap (S:=S) A B x) := by
  simp [pair,RelativeChordAlgebra318.rightPair,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul,RelativeChordAlgebra318.leftPair,RelativeChordAlgebra318.rightPair,map_one]
@[simp] theorem pair_X1 (A B:R) : pair (S:=S) A B (X1 A B)=X1 (a A) (a B) := by simp [X1]
@[simp] theorem pair_X2 (A B:R) : pair (S:=S) A B (X2 A B)=X2 (a A) (a B) := by simp [X2]
@[simp] theorem pair_Y1 (A B:R) : pair (S:=S) A B (Y1 A B)=Y1 (a A) (a B) := by simp [Y1]
@[simp] theorem pair_Y2 (A B:R) : pair (S:=S) A B (Y2 A B)=Y2 (a A) (a B) := by simp [Y2]
@[simp] theorem pair_coeff (A B r:R) : pair (S:=S) A B (coeffMap A B r)=coeffMap (a A) (a B) (a r) := by
  rw [coeffMap,Algebra.ofId_apply,AlgHom.commutes]
  rfl
@[simp] theorem pair_gap (A B:R) : pair (S:=S) A B (RelativeChordAlgebra318.gap A B)=RelativeChordAlgebra318.gap (a A) (a B) := by
  change pair A B (X2 A B-X1 A B)=X2 (a A) (a B)-X1 (a A) (a B)
  simp
@[simp] theorem pair_sum (A B:R) : pair (S:=S) A B (TangentOpenAlgebra318.ordinateSum A B)=TangentOpenAlgebra318.ordinateSum (a A) (a B) := by
  change pair A B (Y1 A B+Y2 A B)=Y1 (a A) (a B)+Y2 (a A) (a B)
  simp
@[simp] theorem pair_denominator (A B:R) (t:Bool) : pair (S:=S) A B (denominator A B t)=denominator (a A) (a B) t := by cases t <;> simp [denominator]
@[simp] theorem pair_slopeNumerator (A B:R) (t:Bool) : pair (S:=S) A B (slopeNumerator A B t)=slopeNumerator (a A) (a B) t := by cases t <;> simp [slopeNumerator,pow_succ]
@[simp] theorem pair_numeratorX (A B:R) (t:Bool) : pair (S:=S) A B (numeratorX A B t)=numeratorX (a A) (a B) t := by simp [numeratorX,pow_succ]
@[simp] theorem pair_numeratorY (A B:R) (t:Bool) : pair (S:=S) A B (numeratorY A B t)=numeratorY (a A) (a B) t := by simp [numeratorY,pow_succ]
@[simp] theorem pair_chartElement (A B:R) (i:Fin 4) : pair (S:=S) A B (FinitePairCover318.chartElement A B i)=FinitePairCover318.chartElement (a A) (a B) i := by
  fin_cases i <;> simpa only [FinitePairCover318.chartElement,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ] using (by first | exact pair_gap (S:=S) A B | exact pair_sum (S:=S) A B | exact pair_numeratorY (S:=S) A B false | exact pair_numeratorY (S:=S) A B true)

@[expose] def localMap (A B:R) (i:Fin 4) :
    FiniteAdditionLocal318.LocalRing A B i →ₐ[R] FiniteAdditionLocal318.LocalRing (a A) (a B) i :=
  IsLocalization.Away.liftAlgHom
    (f:=((FiniteAdditionLocal318.inputMap (a A) (a B) i).restrictScalars R).comp (pair (S:=S) A B))
    (FinitePairCover318.chartElement A B i) (by
      simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,pair_chartElement]
      exact IsLocalization.Away.algebraMap_isUnit (S:=FiniteAdditionLocal318.LocalRing (a A) (a B) i) _)
@[simp] theorem localMap_base (A B:R) (i:Fin 4) (x:PairRing A B) :
    localMap (S:=S) A B i (FiniteAdditionLocal318.inputMap A B i x)=
      FiniteAdditionLocal318.inputMap (a A) (a B) i (pair (S:=S) A B x) := by
  simp only [FiniteAdditionLocal318.inputMap,IsScalarTower.toAlgHom_apply,localMap,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,AlgHom.comp_apply]
  rfl
end FinitePairCoefficient318
