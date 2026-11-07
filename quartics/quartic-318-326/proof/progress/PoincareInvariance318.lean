module
public import PoincareCurvature318
public section
noncomputable section
open Matrix UpperHalfPlane
namespace PoincareInvariance318
open PoincareCurvature318
set_option maxHeartbeats 0

/-- Actual derivative-weighted invariance of the Poincare metric, for every
orientation-preserving real invertible fractional-linear transformation. -/
theorem gl_pullback (g:GL (Fin 2) ℝ) (hg:0<g.val.det) (z:UpperHalfPlane) :
    coefficient (g • z)*‖deriv (fun w:ℂ=>(g • UpperHalfPlane.ofComplex w:UpperHalfPlane):ℂ→ℂ) z‖^2=
      coefficient z := by
  rw [coefficient,coefficient,UpperHalfPlane.im_smul_eq_div_normSq,
    UpperHalfPlane.deriv_smul hg]
  have hd:0<g.det.val:=hg
  have hz:z.im≠0:=z.im_ne_zero
  have hn:‖UpperHalfPlane.denom g z‖≠0:=norm_ne_zero_iff.mpr (UpperHalfPlane.denom_ne_zero g z)
  simp only [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hg,
    abs_of_pos hd,Complex.normSq_eq_norm_sq]
  change 1/(g.val.det*z.im/‖UpperHalfPlane.denom g z‖^2)^2*
    (g.val.det/‖UpperHalfPlane.denom g z‖^2)^2=1/z.im^2
  field_simp

/-- The same identity for the actual determinant-one real matrix subgroup. -/
theorem sl_pullback (g:Matrix.SpecialLinearGroup (Fin 2) ℝ) (z:UpperHalfPlane) :
    coefficient ((Matrix.SpecialLinearGroup.mapGL ℝ g) • z)*
      ‖deriv (fun w:ℂ=>((Matrix.SpecialLinearGroup.mapGL ℝ g) • UpperHalfPlane.ofComplex w:UpperHalfPlane):ℂ→ℂ) z‖^2=
      coefficient z := by
  apply gl_pullback
  have hd:(Matrix.SpecialLinearGroup.mapGL ℝ g).det=1:=Matrix.SpecialLinearGroup.det_mapGL _
  have he:(Matrix.SpecialLinearGroup.mapGL ℝ g).val.det=1:=congrArg Units.val hd
  rw [he]
  norm_num

end PoincareInvariance318
#print axioms PoincareInvariance318.gl_pullback
#print axioms PoincareInvariance318.sl_pullback
