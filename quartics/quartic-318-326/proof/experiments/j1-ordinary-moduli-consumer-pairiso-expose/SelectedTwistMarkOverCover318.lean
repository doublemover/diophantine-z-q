module
public import SelectedOrdinateTorsor318
public import SelectedAffineMarkCoefficient318
public import SelectedSignedMultiplication318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassGluing318
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveTwistPoint318
open SelectedAffineMarkCoefficient318

namespace SelectedTwistMarkOverCover318
variable (n : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => fixed n I τ
variable (hY : IsUnit (ybar n I))
local notation "Y" => hY.unit
local notation "C" => algebraMap R Q (A n)
local notation "D₀" => algebraMap R Q (B n)
local notation "A₁" => twistA n I τ hτ hY
local notation "B₁" => twistB n I τ hτ hY
local notation "a" => algebraMap F Q
local notation "A₂" => a A₁
local notation "B₂" => a B₁
local notation "hA" => (over_original_chart n I τ hτ hY).1
local notation "hB" => (over_original_chart n I τ hτ hY).2.1

@[expose] def twistPoint : Spec (CommRingCat.of F) ⟶ scheme A₁ B₁ :=
  point A₁ B₁ (markEvaluation n I τ hτ hY)

@[expose] def sourcePoint : Spec (CommRingCat.of Q) ⟶ scheme C D₀ :=
  point C D₀ (extendEval (A n) (B n) (q n I))

local notation "v" => (Algebra.ofId F Q).comp (markEvaluation n I τ hτ hY)

@[expose] def changedTwistPoint : Spec (CommRingCat.of Q) ⟶ scheme A₂ B₂ :=
  point A₂ B₂ (extendEval A₁ B₁ v)

local notation "γ" => SelectedPointedShortScaling318.gluedMap A₂ B₂ C D₀ Y hA hB

private theorem eval_x : markEvaluation n I τ hτ hY (ShortAffineJacobian318.x A₁ B₁) =
    markX n I τ hτ hY := AffineEquationFunctor318.toHom_x ..
private theorem eval_y : markEvaluation n I τ hτ hY (ShortAffineJacobian318.y A₁ B₁) =
    markY n I τ hτ hY := AffineEquationFunctor318.toHom_y ..

/-- The particular actual primitive point from the literal chart is taken
to the particular canonical twist section after pullback to the actual cover. -/
theorem same_point :
    sourcePoint n I ≫ γ = changedTwistPoint n I τ hτ hY := by
  unfold sourcePoint changedTwistPoint point
  rw [Category.assoc,SelectedPointedShortScaling318.finite_glued,←Category.assoc]
  unfold SelectedPointedShortScaling318.finiteMap
  rw [←Spec.map_comp]
  congr 1
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply congrArg AlgHom.toRingHom
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,SelectedShortAffineScaling318.hom_x,map_mul,map_pow,
      AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply,extend_x,eval_x]
    change (Y:Q)^2*xbar n I = a (markX n I τ hτ hY)
    exact (over_original_chart n I τ hτ hY).2.2.1.symm
  · simp only [AlgHom.comp_apply,SelectedShortAffineScaling318.hom_y,map_mul,map_pow,
      AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply,extend_y,eval_y]
    change (Y:Q)^3*ybar n I = a (markY n I τ hτ hY)
    exact (over_original_chart n I τ hτ hY).2.2.2.symm

@[reassoc] theorem cover_twist_base :
    changedTwistPoint n I τ hτ hY ≫ WeierstrassCoefficientMap318.coefficientMap A₁ B₁ =
      Spec.algebraMap F Q ≫ twistPoint n I τ hτ hY := by
  unfold changedTwistPoint twistPoint
  rw [point_coefficient,point,point,←Category.assoc,←Spec.map_comp] <;> rfl

@[reassoc] theorem literal_source_base :
    sourcePoint n I ≫ WeierstrassCoefficientMap318.coefficientMap (A n) (B n) =
      point (A n) (B n) (q n I) := by
  unfold sourcePoint
  rw [point_coefficient]

end SelectedTwistMarkOverCover318

#print axioms SelectedTwistMarkOverCover318.same_point
#print axioms SelectedTwistMarkOverCover318.cover_twist_base
