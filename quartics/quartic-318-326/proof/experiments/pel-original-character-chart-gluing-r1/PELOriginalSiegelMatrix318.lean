module
public import PELOriginalSymplecticCoordinates318
public section
noncomputable section
namespace PELOriginalSiegelMatrix318
open PELQuaternionRealRepresentation318
variable (τ:ℂ)
/-- Explicit normalized period matrix of the SAME original quaternionic
order in its integral symplectic basis. -/
@[expose] def omega:Matrix (Fin 2) (Fin 2) ℂ:=
  !![(alpha:ℂ)/10*((3+(beta:ℂ))*τ+((beta:ℂ)-3)/τ),
      -(alpha:ℂ)/10*((1+(beta:ℂ))*τ+((beta:ℂ)-1)/τ);
     -(alpha:ℂ)/10*((1+(beta:ℂ))*τ+((beta:ℂ)-1)/τ),
      (alpha:ℂ)/5*(τ-1/τ)]
lemma symmetric:(omega τ).transpose=omega τ:=by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
@[expose] def imaginary:Matrix (Fin 2) (Fin 2) ℝ:=fun i j=>(omega τ i j).im
@[expose] def energy (x:Fin 2→ℝ):ℝ:=
  x 0*(imaginary τ 0 0*x 0+imaginary τ 0 1*x 1)+
    x 1*(imaginary τ 1 0*x 0+imaginary τ 1 1*x 1)
lemma im_inverse:(1/τ).im= -τ.im/Complex.normSq τ:=by
  simp [Complex.inv_im]
lemma energy_squares (x:Fin 2→ℝ):
    energy τ x=alpha*τ.im/20*
      (((beta+1)*x 0-2*x 1)^2+((beta-1)*x 0+2*x 1)^2/Complex.normSq τ):=by
  by_cases ht:τ=0
  · subst τ
    simp [energy,imaginary,omega]
  have hn:Complex.normSq τ≠0:=(Complex.normSq_pos.mpr ht).ne'
  simp [energy,imaginary,omega,Complex.mul_im,Complex.div_im]
  field_simp [hn]
  ring_nf
  simp only [beta_sq]
  ring

/-- Strict positive definiteness is proved from an explicit sum of two
squares. Both squares can vanish only at zero since beta=sqrt5 is nonzero. -/
lemma positive (hτ:0<τ.im) (x:Fin 2→ℝ) (hx:x≠0):0<energy τ x:=by
  have ht:τ≠0:=by intro h;simpa [h] using hτ
  have hn:0<Complex.normSq τ:=Complex.normSq_pos.mpr ht
  have h1:=sq_nonneg ((beta+1)*x 0-2*x 1)
  have h2:=sq_nonneg ((beta-1)*x 0+2*x 1)
  have hs:0<((beta+1)*x 0-2*x 1)^2+
      ((beta-1)*x 0+2*x 1)^2/Complex.normSq τ:=by
    apply lt_of_le_of_ne (add_nonneg h1 (div_nonneg h2 hn.le))
    intro he
    have ha:((beta+1)*x 0-2*x 1)^2=0:=by
      have hd:=div_nonneg h2 hn.le
      linarith
    have hb:((beta-1)*x 0+2*x 1)^2=0:=by
      have hz:((beta-1)*x 0+2*x 1)^2/Complex.normSq τ=0:=by linarith
      exact (div_eq_zero_iff).mp hz |>.resolve_right hn.ne'
    have e1:=sq_eq_zero_iff.mp ha
    have e2:=sq_eq_zero_iff.mp hb
    have hbx:beta*x 0=0:=by linarith
    have hx0: x 0=0:=(mul_eq_zero.mp hbx).resolve_left beta_pos.ne'
    have hx1:x 1=0:=by rw [hx0] at e1;linarith
    apply hx
    ext i
    fin_cases i <;> assumption
  rw [energy_squares]
  exact mul_pos (div_pos (mul_pos alpha_pos hτ) (by norm_num)) hs
end PELOriginalSiegelMatrix318
