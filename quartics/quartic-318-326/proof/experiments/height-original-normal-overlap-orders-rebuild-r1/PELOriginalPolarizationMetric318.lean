module
public import PELOriginalPolarizationAutomorphy318
public section
noncomputable section
namespace PELOriginalPolarizationMetric318
open QuaternionicRealPeriod318 PELPeriodRiemannForm318 PELOriginalHermitianForm318
open PELOriginalPolarizationAutomorphy318
variable (τ:ℂ) (hτ:0<τ.im)
local notation "E" => riemann τ hτ
@[expose] def weight (z:ComplexVectors):ℝ:=Real.exp (-Real.pi*E z (Complex.I • z))
lemma weight_positive (z:ComplexVectors):0<weight τ hτ z:=Real.exp_pos _
lemma symmetric_real (z w:ComplexVectors):E w (Complex.I • z)=E z (Complex.I • w):=by
  rw [skew,I_move]
  ring
lemma diagonal_translate (z w:ComplexVectors):
    E (z+w) (Complex.I • (z+w))=
      E z (Complex.I • z)+2*E z (Complex.I • w)+E w (Complex.I • w):=by
  rw [smul_add,add_left,add_right,add_right,symmetric_real τ hτ z w]
  ring
lemma exponent_real (l:L τ hτ) (z:ComplexVectors):
    (exponent τ hτ l z).re=
      Real.pi*(E z (Complex.I • l.val)+E l.val (Complex.I • l.val)/2):=by
  simp [exponent,real_part]

/-- The genuine automorphy factor preserves the positive Gaussian metric
on the original trivial line over C². The lattice phase contributes no
real part, and the sign of H matches the original positive Riemann form. -/
lemma factor_metric (l:L τ hτ) (z:ComplexVectors):
    ‖factor τ hτ l z‖^2*weight τ hτ (z+l.val)=weight τ hτ z:=by
  rw [factor,Complex.norm_exp,exponent_real]
  simp only [weight,pow_two,←Real.exp_add]
  congr 1
  rw [diagonal_translate]
  ring

@[expose] def squaredNorm (p:ComplexVectors×ℂ):ℝ:=‖p.2‖^2*weight τ hτ p.1
lemma squaredNorm_nonnegative (p:ComplexVectors×ℂ):0≤squaredNorm τ hτ p:=
  mul_nonneg (sq_nonneg _) (weight_positive τ hτ p.1).le
lemma squaredNorm_zero_iff (p:ComplexVectors×ℂ):squaredNorm τ hτ p=0↔p.2=0:=by
  simp [squaredNorm,mul_eq_zero,(weight_positive τ hτ p.1).ne',sq_eq_zero_iff]
lemma squaredNorm_action (l:L τ hτ) (p:ComplexVectors×ℂ):
    squaredNorm τ hτ (action τ hτ l p)=squaredNorm τ hτ p:=by
  simp only [squaredNorm,action,norm_mul,mul_pow]
  calc
    _=‖p.2‖^2*(‖factor τ hτ l p.1‖^2*weight τ hτ (p.1+l.val)):=by ring
    _=_:=by rw [factor_metric]
end PELOriginalPolarizationMetric318
