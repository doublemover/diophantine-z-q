module
public import PELOriginalThetaHermitianGauge318
public import PELOriginalNormalizedHermitianMatrix318
public section
noncomputable section
namespace PELOriginalThetaGaugeMatrix318
open QuaternionicRealPeriod318 PELOriginalNormalizedHermitianMatrix318
open PELOriginalSiegelMatrix318 PELOriginalSiegelNormalization318 PELOriginalSymplecticCoordinates318
open PELOriginalThetaConvergence318
variable (τ:ℂ) (hτ:0<τ.im)

@[expose] def bilinearMap:ComplexVectors→ₗ[ℂ]ComplexVectors→ₗ[ℂ]ℂ where
  toFun z:=
    { toFun:=bilinear τ z
      map_add':=by intro w v;simp [bilinear];ring
      map_smul':=by intro a w;simp [bilinear];ring }
  map_add':=by intro z w;ext v;simp [bilinear];ring
  map_smul':=by intro a z;ext v;simp [bilinear];ring
lemma symmetric (z w:ComplexVectors):bilinearMap τ z w=bilinearMap τ w z:=by
  change bilinear τ z w=bilinear τ w z
  unfold bilinear
  ring
lemma conjugate_omega (i j:Fin 2):
    star (omega τ i j)=omega τ i j-2*Complex.I*(imaginary τ i j:ℂ):=by
  apply Complex.ext <;> simp [imaginary,Complex.mul_re,Complex.mul_im] <;> ring

/-- The precise imaginary-period identity needed by the quadratic gauge,
now derived from the ACTUAL G*Im(Omega)=1 and original Hermitian comparison. -/
theorem period_difference (p:Pair) (z:ComplexVectors):
    bilinearMap τ z (standardPeriod τ p)-normalizedHermitian τ hτ z (standardPeriod τ p)=
      2*Complex.I*linear (p.2 0,p.2 1) z:=by
  have hm:=gram_imaginary_inverse τ hτ
  have h00:=congrArg (fun M:Matrix (Fin 2) (Fin 2) ℝ=>(M 0 0:ℂ)) hm
  have h01:=congrArg (fun M:Matrix (Fin 2) (Fin 2) ℝ=>(M 0 1:ℂ)) hm
  have h10:=congrArg (fun M:Matrix (Fin 2) (Fin 2) ℝ=>(M 1 0:ℂ)) hm
  have h11:=congrArg (fun M:Matrix (Fin 2) (Fin 2) ℝ=>(M 1 1:ℂ)) hm
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,
    Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_one,Complex.ofReal_zero,
    show gram τ 1 0=gram τ 0 1 from rfl,ite_true,ite_false,Fin.reduceEq] at h00 h01 h10 h11
  rw [normalizedHermitian_formula]
  change bilinear τ z (standardPeriod τ p)-bilinear τ z (conjugate (standardPeriod τ p))=_
  simp only [bilinear,conjugate,standardPeriod,linear,star_add,star_mul,star_intCast,conjugate_omega]
  linear_combination
    (2*Complex.I*z 0*(p.2 0:ℂ))*h00+
    (2*Complex.I*z 0*(p.2 1:ℂ))*h01+
    (2*Complex.I*z 1*(p.2 0:ℂ))*h10+
    (2*Complex.I*z 1*(p.2 1:ℂ))*h11

/-- The exact gauge identity has no matrix/form compatibility premise at
its original-source endpoint. Neither characteristic nor period lattice changes. -/
theorem original_multiplier (p:Pair) (z:ComplexVectors):
    PELOriginalThetaHermitianGauge318.gauge (bilinearMap τ) (z+standardPeriod τ p)*
      PELOriginalThetaQuasiperiods318.multiplier τ (p.2 0,p.2 1) z=
    normalizedFactor τ hτ p z*PELOriginalThetaHermitianGauge318.gauge (bilinearMap τ) z:=
  PELOriginalThetaHermitianGauge318.exact_multiplier τ hτ (bilinearMap τ)
    (symmetric τ) (period_difference τ hτ) p z
end PELOriginalThetaGaugeMatrix318
