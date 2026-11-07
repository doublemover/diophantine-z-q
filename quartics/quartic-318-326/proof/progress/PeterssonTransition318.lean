module
public import PoincareInvariance318
public import PeterssonSectionNorm318
public section
noncomputable section
open PoincareCurvature318 PeterssonSectionNorm318 Matrix
namespace PeterssonTransition318
set_option maxHeartbeats 0

/-- Genuine bicanonical coordinate transition under an actual real fractional
linear map. The coefficient transforms by the square of its complex derivative. -/
theorem quadratic_transition (g:GL (Fin 2) ℝ) (hg:0<g.val.det)
    (z:UpperHalfPlane) (q:ℂ) :
    quadraticNorm (coefficient z)
      (q*(deriv (fun w:ℂ=>(g • UpperHalfPlane.ofComplex w:UpperHalfPlane):ℂ→ℂ) z)^2)=
    quadraticNorm (coefficient (g • z)) q := by
  let d:ℂ:=deriv (fun w:ℂ=>(g • UpperHalfPlane.ofComplex w:UpperHalfPlane):ℂ→ℂ) z
  have hd:d≠0:=UpperHalfPlane.deriv_smul_ne_zero hg z
  have hn:‖d‖≠0:=norm_ne_zero_iff.mpr hd
  have hp:coefficient (g • z)≠0:=(coefficient_positive _).ne'
  have hi:coefficient z=coefficient (g • z)*‖d‖^2:=
    (PoincareInvariance318.gl_pullback g hg z).symm
  change quadraticNorm (coefficient z) (q*d^2)=_
  rw [quadraticNorm_formula _ (coefficient_positive _),quadraticNorm_formula _ (coefficient_positive _),
    norm_mul,norm_pow,hi]
  field_simp

/-- In the uniformizing coordinate the genuine bicanonical coefficient norm is
exactly |q|*(2 Im tau)^2. -/
theorem uniformizing_norm (z:UpperHalfPlane) (q:ℂ) :
    quadraticNorm (coefficient z) q=‖q‖*(2*z.im)^2 := by
  rw [quadraticNorm,cotangent_normalization]

end PeterssonTransition318
#print axioms PeterssonTransition318.quadratic_transition
