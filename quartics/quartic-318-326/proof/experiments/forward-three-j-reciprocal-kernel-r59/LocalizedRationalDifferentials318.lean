module
public import FramedRelativeDifferentials318
public section
noncomputable section
namespace LocalizedRationalDifferentials318
open Polynomial KaehlerDifferential
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Ring (h : ℚ[X]) := Localization.Away h
@[expose] def value (h : ℚ[X]) : ℚ[X] →ₐ[ℚ] Ring h := IsScalarTower.toAlgHom ℚ ℚ[X] (Ring h)
@[expose] def frame (h : ℚ[X]) : KaehlerDifferential ℚ (Ring h) ≃ₗ[Ring h] Ring h :=
  LocalizedKaehlerFrame318.localFrame (Submonoid.powers h) (KaehlerDifferential.polynomialEquiv ℚ)
@[expose] def differential (h : ℚ[X]) : Derivation ℚ (Ring h) (Ring h) :=
  KaehlerDifferential.linearMapEquivDerivation ℚ (Ring h) (frame h).toLinearMap

lemma differential_value (h p : ℚ[X]) : differential h (value h p)=value h p.derivative := by
  change frame h (D ℚ (Ring h) (algebraMap ℚ[X] (Ring h) p))=_
  rw [frame,LocalizedKaehlerFrame318.localFrame_D,KaehlerDifferential.polynomialEquiv_D]
  rfl

variable (f g h : ℚ[X]) (u : Ring h)

lemma differential_inverse (hu : value h f*u=1) : differential h u= -u^2*value h f.derivative := by
  have hd := congrArg (differential h) hu
  rw [Derivation.leibniz,differential_value,Derivation.map_one_eq_zero,smul_eq_mul,smul_eq_mul] at hd
  calc
    differential h u=(value h f*u)*differential h u := by rw [hu,one_mul]
    _ = u*(value h f*differential h u) := by ring
    _ = u*(-(u*value h f.derivative)) := by rw [eq_neg_of_add_eq_zero_left hd]
    _ = _ := by ring

@[expose] def targetCoordinate : Ring h := value h g*u

lemma differential_ratio (hu : value h f*u=1) : differential h (targetCoordinate g h u)=
    value h (g.derivative*f-g*f.derivative)*u^2 := by
  rw [targetCoordinate,Derivation.leibniz,differential_inverse f h u hu,differential_value]
  simp only [smul_eq_mul,map_sub,map_mul]
  linear_combination -(value h g.derivative)*u*hu

/-- A second polynomial-ring scalar action is required here: it sends the
target coordinate to g/f, not the source coordinate to T. -/
@[expose,instance_reducible] def targetAlgebra : Algebra ℚ[X] (Ring h) :=
  (Polynomial.aeval (R:=ℚ) (targetCoordinate g h u)).toRingHom.toAlgebra
/-- Pin all three scalar actions to the algebra structures. Localization
also supplies a direct source-coordinate SMul instance; it must not replace
the distinct target-coordinate action while elaborating this tower. -/
lemma targetTower :
    letI := targetAlgebra g h u
    letI : SMul ℚ ℚ[X] := (inferInstance : Algebra ℚ ℚ[X]).toSMul
    letI : SMul ℚ (Ring h) := (inferInstance : Algebra ℚ (Ring h)).toSMul
    letI : SMul ℚ[X] (Ring h) := (targetAlgebra g h u).toSMul
    IsScalarTower ℚ ℚ[X] (Ring h) := by
  letI := targetAlgebra g h u
  letI : SMul ℚ ℚ[X] := (inferInstance : Algebra ℚ ℚ[X]).toSMul
  letI : SMul ℚ (Ring h) := (inferInstance : Algebra ℚ (Ring h)).toSMul
  letI : SMul ℚ[X] (Ring h) := (targetAlgebra g h u).toSMul
  apply IsScalarTower.of_algebraMap_eq
  intro q
  exact ((Polynomial.aeval (R:=ℚ) (targetCoordinate g h u)).commutes q).symm

lemma actual_jacobian (hu : value h f*u=1) :
    letI := targetAlgebra g h u
    FramedRelativeDifferentials318.jacobian (frame h)=
      value h (g.derivative*f-g*f.derivative)*u^2 := by
  letI := targetAlgebra g h u
  unfold FramedRelativeDifferentials318.jacobian FramedRelativeDifferentials318.coordinate
  change frame h (D ℚ (Ring h) (Polynomial.aeval (R:=ℚ) (targetCoordinate g h u) X))=_
  rw [Polynomial.aeval_X]
  exact differential_ratio f g h u hu

/-- Exact relative Kähler module of a rational coordinate on an actual
localized source chart. The quotient is by the full Jacobian coefficient. -/
@[expose] def relativePresentation (hu : value h f*u=1) :
    letI := targetAlgebra g h u
    (Ring h ⧸ Ideal.span {value h (g.derivative*f-g*f.derivative)*u^2}) ≃ₗ[Ring h]
      KaehlerDifferential ℚ[X] (Ring h) := by
  letI := targetAlgebra g h u
  letI : SMul ℚ ℚ[X] := (inferInstance : Algebra ℚ ℚ[X]).toSMul
  letI : SMul ℚ (Ring h) := (inferInstance : Algebra ℚ (Ring h)).toSMul
  letI : SMul ℚ[X] (Ring h) := (targetAlgebra g h u).toSMul
  letI := targetTower g h u
  rw [←actual_jacobian f g h u hu]
  exact FramedRelativeDifferentials318.quotientEquiv (frame h)

end LocalizedRationalDifferentials318
