module
public import PELOriginalHermitianCoordinates318
public import PELOriginalThetaQuasiperiods318
public section
noncomputable section
namespace PELOriginalNormalizedHermitianMatrix318
open QuaternionicRealPeriod318 PELQuaternionRealRepresentation318
open PELOriginalSiegelMatrix318 PELOriginalSiegelNormalization318
open PELOriginalHermitianCoordinates318
variable (τ:ℂ) (hτ:0<τ.im)
/-- REAL coefficient matrix of the actual normalized Hermitian form.
This is derived from the genuine original a-period matrix, not selected
as an unrelated positive form. -/
@[expose] def gram:Matrix (Fin 2) (Fin 2) ℝ:=
  !![(Complex.normSq τ+1)/(alpha*τ.im),
      ((1+beta)*Complex.normSq τ+1-beta)/(2*alpha*τ.im);
     ((1+beta)*Complex.normSq τ+1-beta)/(2*alpha*τ.im),
      ((3+beta)*Complex.normSq τ+3-beta)/(2*alpha*τ.im)]
lemma gram_symmetric:(gram τ).transpose=gram τ:=by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
@[expose] def bilinear (z w:ComplexVectors):ℂ:=
  (gram τ 0 0:ℂ)*z 0*w 0+(gram τ 0 1:ℂ)*(z 0*w 1+z 1*w 0)+
    (gram τ 1 1:ℂ)*z 1*w 1
@[expose] def conjugate (z:ComplexVectors):ComplexVectors:=fun j=>star (z j)
/-- Equality on ALL original complex tangent vectors, including all
cross terms, to the same normalized H used in the existing factors. -/
lemma normalizedHermitian_formula (z w:ComplexVectors):
    normalizedHermitian τ hτ z w=bilinear τ z (conjugate w):=by
  rw [normalizedHermitian,form_coordinates]
  change (denormalize τ z 0*star (denormalize τ w 0)+
    denormalize τ z 1*star (denormalize τ w 1))/((alpha*τ.im:ℝ):ℂ)=_
  apply Complex.ext <;>
    simp [denormalize,bilinear,conjugate,gram,Complex.mul_re,Complex.mul_im,
      Complex.div_re,Complex.div_im,Complex.normSq_apply] <;>
    field_simp [alpha_pos.ne',hτ.ne'] <;>
    ring_nf <;> simp only [beta_sq] <;> ring

/-- Exact inverse relation to the imaginary part of the ACTUAL normalized
period matrix. This supplies the theta gauge with no new matrix hypothesis. -/
lemma gram_imaginary_inverse:gram τ*imaginary τ=1:=by
  have hn:Complex.normSq τ≠0:=
    (Complex.normSq_pos.mpr (parameter_ne τ hτ)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram,imaginary,omega,Matrix.mul_apply,Fin.sum_univ_two,
      Complex.mul_im,Complex.div_im] <;>
    field_simp [hn,alpha_pos.ne',hτ.ne'] <;>
    ring_nf <;> simp only [beta_sq] <;> ring
lemma imaginary_gram_inverse:imaginary τ*gram τ=1:=by
  have h:=congrArg Matrix.transpose (gram_imaginary_inverse τ hτ)
  simpa only [Matrix.transpose_mul,Matrix.transpose_one,gram_symmetric,
    show (imaginary τ).transpose=imaginary τ from by ext i j;fin_cases i <;> fin_cases j <;> rfl] using h
end PELOriginalNormalizedHermitianMatrix318
