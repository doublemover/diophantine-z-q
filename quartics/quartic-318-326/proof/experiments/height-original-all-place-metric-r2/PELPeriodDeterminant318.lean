module
public import PELOriginalUnitBiholomorph318
public section
noncomputable section
namespace PELPeriodDeterminant318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318 QuaternionicUnitPeriodTransport318
open scoped Manifold ContDiff
set_option maxHeartbeats 1200000

/-- The real splitting has determinant equal to the original rational
reduced norm. This fixes the arithmetic norm-one condition on the action. -/
theorem representation_det (x : B) : (representation x).det=(reducedNorm x:ℝ) := by
  change (matrix x).det=(reducedNorm x:ℝ)
  rw [Matrix.det_fin_two]
  change ((x.re:ℝ)+beta*(x.imJ:ℝ))*((x.re:ℝ)-beta*(x.imJ:ℝ))-
    (-alpha*(x.imI:ℝ)+alpha*beta*(x.imK:ℝ))*
      (alpha*(x.imI:ℝ)+alpha*beta*(x.imK:ℝ))=(reducedNorm x:ℝ)
  simp only [reducedNorm]
  push_cast
  calc
    _ = (x.re:ℝ)^2+alpha^2*(x.imI:ℝ)^2-beta^2*(x.imJ:ℝ)^2-
        alpha^2*beta^2*(x.imK:ℝ)^2 := by ring
    _ = _ := by rw [alpha_sq,beta_sq]; ring

@[expose] def complexMatrix (x : B) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (representation x i j:ℂ)

/-- This is the actual complex-linear order action on the period carrier. -/
theorem complexMatrix_action (x : B) (z : ComplexVectors) :
    Matrix.mulVec (complexMatrix x) z=leftLinear (representation x) z := by
  funext i
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,complexMatrix,
    leftLinear,LinearMap.coe_mk,AddHom.coe_mk,action]

/-- The analytic period-carrier determinant condition; identification with
an algebraic abelian scheme's Lie module remains a separate construction. -/
theorem complexMatrix_det (x : B) : (complexMatrix x).det=(reducedNorm x:ℂ) := by
  have h := representation_det x
  simp only [Matrix.det_fin_two] at h ⊢
  unfold complexMatrix
  exact_mod_cast h

theorem normOne_determinant (u : orderˣ) (hu : reducedNorm ((u:order):B)=1) :
    (unitMatrix representation order u).det=1 := by
  change (representation ((u:order):B)).det=1
  rw [representation_det,hu]
  all_goals norm_num

/-- Fiber transport now takes the original reduced-norm-one units, not an
unrelated determinant-one matrix. -/
@[expose] def normOneTransport (u : orderˣ) (hu : reducedNorm ((u:order):B)=1)
    (τ : ℂ) (hτ : 0<τ.im) : PELComplexPeriodSurface318.Surface τ ≃+
      PELComplexPeriodSurface318.Surface (PELOriginalUnitBiholomorph318.parameter u τ) :=
  PELOriginalUnitBiholomorph318.transport u (normOne_determinant u hu) τ hτ

theorem normOneTransport_holomorphic (u : orderˣ) (hu : reducedNorm ((u:order):B)=1)
    (τ : ℂ) (hτ : 0<τ.im) :
    letI := PELComplexPeriodSurface318.surfaceCharts τ hτ
    letI := PELComplexPeriodSurface318.surfaceCharts (PELOriginalUnitBiholomorph318.parameter u τ)
      (PELOriginalUnitBiholomorph318.parameter_positive u (normOne_determinant u hu) τ hτ)
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω (normOneTransport u hu τ hτ) :=
  PELOriginalUnitBiholomorph318.transport_holomorphic u (normOne_determinant u hu) τ hτ
end PELPeriodDeterminant318
