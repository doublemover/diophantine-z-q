module
public import ProjectivePrincipalTrivializationNatural318
public import ProjectiveKernelParameter318
public section
noncomputable section
namespace ProjectiveKernelNormalizationEquations318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "eqn" => ProjectiveKernelEquations318.equation R P Q d
variable (i : Fin F.size)
@[expose] def principalEquation (φ : Module.Dual R Q) : H i :=
  ProjectiveParameterPrincipalNormalization318.point R P i (eqn φ)
@[expose] def sliceEquation (φ : Module.Dual R Q) : B i :=
  Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P i) (eqn φ)
variable (S : Type) [CommRing S] [Algebra R S]
local notation "E" => ProjectivePrincipalUnitTrivialization318.trivialization R P i (CommRingCat.of S)
/-- The ACTUAL normalized differential equation is the original equation
multiplied by the inverse of the selected unit coordinate. -/
lemma normalized_equation (a : H i →ₐ[R] S) (φ : Module.Dual R Q) :
    (E a).2 (sliceEquation R P Q d i φ)=
      (((E a).1⁻¹:Sˣ):S)*a (principalEquation R P Q d i φ) := by
  change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (eqn φ))=_
  rw [Ideal.Quotient.lift_mk]
  exact ProjectiveParameterUnitAction318.pointScale_generator R P S _ _ (φ.comp d)
/-- Normalizing preserves ALL genuine linear kernel equations, in both
directions and over nonreduced rings. Nonzero is never substituted for unit. -/
lemma vanishing_iff (a : H i →ₐ[R] S) :
    (∀ φ,a (principalEquation R P Q d i φ)=0) ↔
      ∀ φ,(E a).2 (sliceEquation R P Q d i φ)=0 := by
  constructor
  · intro h φ
    rw [normalized_equation,h φ,mul_zero]
  · intro h φ
    have he := congrArg (fun x : S => ((E a).1:S)*x) (h φ)
    rw [normalized_equation,←mul_assoc,Units.mul_inv,one_mul,mul_zero] at he
    exact he

end ProjectiveKernelNormalizationEquations318
