module
public import SelectedCanonicalMarkedConverse318
public import SelectedPointedShortScaling318
public import SelectedAffineMarkCoefficient318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassGluing318
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveTwistPoint318
open SelectedMarkedNormalization318 SelectedCanonicalMarkedConverse318
open SelectedAffineMarkCoefficient318

namespace SelectedCanonicalCompletedConverse318
variable (n : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => fixed n I τ
variable (hY : IsUnit (ybar n I))
local notation "A₀" => twistA n I τ hτ hY
local notation "B₀" => twistB n I τ hτ hY
local notation "m₀" => markEvaluation n I τ hτ hY

variable (S : Type) [CommRing S] [Algebra R S] (f : F →ₐ[R] S)
local notation "A₁" => f A₀
local notation "B₁" => f B₀

/-- Coefficient change of the actual canonical point along the constructed
inverse class, as the actual affine equation AlgHom. -/
@[expose] def changedEval : ShortAffineJacobian318.Ring A₁ B₁ →ₐ[S] S := by
  letI : Algebra F S := f.toRingHom.toAlgebra
  exact extendEval A₀ B₀ ((Algebra.ofId F S).comp m₀)

@[simp] theorem changed_x : changedEval n I τ hτ hY S f (ShortAffineJacobian318.x A₁ B₁) =
    f (markX n I τ hτ hY) := by
  letI : Algebra F S := f.toRingHom.toAlgebra
  rw [changedEval,extend_x,AlgHom.comp_apply,markEvaluation,
    AffineEquationFunctor318.toHom_x] <;> rfl

@[simp] theorem changed_y : changedEval n I τ hτ hY S f (ShortAffineJacobian318.y A₁ B₁) =
    f (markY n I τ hτ hY) := by
  letI : Algebra F S := f.toRingHom.toAlgebra
  rw [changedEval,extend_y,AlgHom.comp_apply,markEvaluation,
    AffineEquationFunctor318.toHom_y] <;> rfl

@[reassoc] theorem changed_mark_base :
    point A₁ B₁ (changedEval n I τ hτ hY S f) ≫
        WeierstrassCoefficientMap318.coefficientMap (S:=S) A₀ B₀ =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ point A₀ B₀ m₀ := by
  letI : Algebra F S := f.toRingHom.toAlgebra
  rw [changedEval,point_coefficient,point,point,←Category.assoc,←Spec.map_comp] <;> rfl

/-- On the actual canonical twist, the short coefficient ratio is the
chosen twist unit: its square/cube give the displayed coefficients.
Dividing that canonical mark by the same unit reads the original x. -/
theorem canonical_read :
    abscissa (Units.map f.toMonoidHom (twistUnit n I τ hτ hY))
      (f (markX n I τ hτ hY)) = f (fixedX n I τ hτ) := by
  let d := Units.map f.toMonoidHom (twistUnit n I τ hτ hY)
  simp only [markX,map_mul,abscissa]
  change (↑d⁻¹:S)*((d:S)*f (fixedX n I τ hτ)) = _
  rw [←mul_assoc,Units.inv_mul,one_mul]

variable (C D' : S) (P : ShortAffineJacobian318.Ring C D' →ₐ[S] S)
local notation "x" => P (ShortAffineJacobian318.x C D')
local notation "y" => P (ShortAffineJacobian318.y C D')
variable (c Y : Sˣ) (hYP : (Y:S) = y)
variable (hC : C = (c:S)^2 * algebraMap R S (A n))
variable (hD : D' = (c:S)^3 * algebraMap R S (B n))
variable (hx : f (fixedX n I τ hτ) = abscissa c x)
local notation "d" => Units.map f.toMonoidHom (twistUnit n I τ hτ hY)
local notation "ρ" => recoveryScale c d Y
local notation "eqs" => transport_eqs n I τ hτ S c hY f C D' P Y hYP hC hD hx

/-- The arbitrary given genuine marked short curve is isomorphic to the
specific pullback along f of the canonical short curve. The named map uses
the original two genuine affine/infinity gluing charts. -/
@[expose] def recoverIso : scheme C D' ≅ scheme A₁ B₁ :=
  SelectedPointedShortScaling318.iso A₁ B₁ C D' ρ eqs.1 eqs.2.1

local notation "γ" => (recoverIso n I τ hτ hY S f C D' P c Y hYP hC hD hx).hom

include hYP hC hD hx in
@[reassoc] theorem recover_over :
    γ ≫ structureMap A₁ B₁ = structureMap C D' :=
  SelectedPointedShortScaling318.glued_base A₁ B₁ C D' ρ eqs.1 eqs.2.1

include hYP hC hD hx in
@[reassoc] theorem recover_zero :
    infinity C D' ≫ γ = infinity A₁ B₁ :=
  SelectedPointedShortScaling318.zero_preserved A₁ B₁ C D' ρ eqs.1 eqs.2.1

include hYP hC hD hx in
/-- Equality of the embedded marked Scheme points, not just the two
points' coordinates after an unspecified field extension. -/
@[reassoc] theorem recover_mark :
    point C D' P ≫ γ = point A₁ B₁ (changedEval n I τ hτ hY S f) := by
  unfold recoverIso point
  change (Spec.map (CommRingCat.ofHom P.toRingHom) ≫ finiteChart C D') ≫
      SelectedPointedShortScaling318.gluedMap A₁ B₁ C D' ρ eqs.1 eqs.2.1 = _
  rw [Category.assoc,SelectedPointedShortScaling318.finite_glued,←Category.assoc]
  unfold SelectedPointedShortScaling318.finiteMap
  rw [←Spec.map_comp]
  congr 1
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply congrArg AlgHom.toRingHom
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,SelectedShortAffineScaling318.hom_x,map_mul,map_pow,
      AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply,changed_x]
    exact eqs.2.2.1.symm
  · simp only [AlgHom.comp_apply,SelectedShortAffineScaling318.hom_y,map_mul,map_pow,
      AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply,changed_y]
    exact eqs.2.2.2.symm

end SelectedCanonicalCompletedConverse318

#print axioms SelectedCanonicalCompletedConverse318.canonical_read
#print axioms SelectedCanonicalCompletedConverse318.changed_mark_base
#print axioms SelectedCanonicalCompletedConverse318.recover_zero
#print axioms SelectedCanonicalCompletedConverse318.recover_mark
