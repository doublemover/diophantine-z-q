module
public import EntirePeriodicDoubleIntegral318
public import PELOriginalThetaHolomorphy318
public section
noncomputable section
namespace EntireDoubleFourierTranslation318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318
open EntirePeriodicDoubleIntegral318 Complex intervalIntegral
@[expose] def character (k:Index) (z:ComplexVectors):ℂ:=
  Complex.exp (2*(Real.pi:ℂ)*Complex.I*linear k z)
@[expose] def weight (k:Index) (z:ComplexVectors):ℂ:=
  Complex.exp (-2*(Real.pi:ℂ)*Complex.I*linear k z)
lemma weight_add(k:Index)(z w:ComplexVectors):weight k (z+w)=weight k z*weight k w:=by
  simp only [weight,linear,Pi.add_apply]
  rw [←Complex.exp_add]
  congr 1
  ring
lemma character_weight(k:Index)(z:ComplexVectors):character k z*weight k z=1:=by
  rw [character,weight,←Complex.exp_add]
  convert Complex.exp_zero using 1 <;> ring
lemma weight_holomorphic(k:Index):Differentiable ℂ (weight k):=
  Complex.differentiable_exp.comp
    ((PELOriginalThetaHolomorphy318.linearMap k).differentiable.const_mul _)
lemma weight_first_period(k:Index)(x y:ℂ):weight k ![x+1,y]=weight k ![x,y]:=by
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨-k.1,?_⟩
  simp only [linear,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring
lemma weight_second_period(k:Index)(x y:ℂ):weight k ![x,y+1]=weight k ![x,y]:=by
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨-k.2,?_⟩
  simp only [linear,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring
@[expose] def weighted (f:ComplexVectors→ℂ) (k:Index)(z:ComplexVectors):ℂ:=f z*weight k z
@[expose] def coefficient(f:ComplexVectors→ℂ)(k:Index):ℂ:=periodIntegral (weighted f k) 0
@[expose] def translate(f:ComplexVectors→ℂ)(w:ComplexVectors)(z:ComplexVectors):ℂ:=f (z+w)
lemma coordinate_add(x y:ℂ)(w:ComplexVectors):![x+w 0,y+w 1]=![x,y]+w:=by
  ext i
  fin_cases i <;> simp
lemma periodIntegral_mul(c:ℂ)(f:ComplexVectors→ℂ)(w:ComplexVectors):
    periodIntegral (fun z=>c*f z) w=c*periodIntegral f w:=by
  simp only [periodIntegral]
  simp_rw [intervalIntegral.integral_const_mul]
lemma weighted_translate(f:ComplexVectors→ℂ)(k:Index)(w:ComplexVectors):
    periodIntegral (weighted f k) w=weight k w*coefficient (translate f w) k:=by
  simp only [periodIntegral,weighted,coefficient,translate,Pi.zero_apply,add_zero]
  simp_rw [coordinate_add,weight_add]
  have he:∀x y:ℝ,f (![ (x:ℂ),(y:ℂ)]+w)*
      (weight k ![(x:ℂ),(y:ℂ)]*weight k w)=
      weight k w*(f (![(x:ℂ),(y:ℂ)]+w)*weight k ![(x:ℂ),(y:ℂ)]):=by
    intro x y
    ring
  simp_rw [he,intervalIntegral.integral_const_mul]

/-- Fourier coefficients of the ACTUAL entire integer-periodic
function obey the full complex translation law. The horizontal-cycle
movement and both integral interchanges have already been constructed. -/
theorem coefficient_translation(f:ComplexVectors→ℂ)(hf:Differentiable ℂ f)
    (h0:∀x y:ℂ,f ![x+1,y]=f ![x,y])
    (h1:∀x y:ℂ,f ![x,y+1]=f ![x,y]) (k:Index)(w:ComplexVectors):
    coefficient (translate f w) k=character k w*coefficient f k:=by
  have hg:Differentiable ℂ (weighted f k):=hf.mul (weight_holomorphic k)
  have hp0:∀x y:ℂ,weighted f k ![x+1,y]=weighted f k ![x,y]:=by
    intro x y
    simp only [weighted,h0,weight_first_period]
  have hp1:∀x y:ℂ,weighted f k ![x,y+1]=weighted f k ![x,y]:=by
    intro x y
    simp only [weighted,h1,weight_second_period]
  have hs:=period_shift (weighted f k) hg hp0 hp1 w
  rw [weighted_translate] at hs
  change weight k w*coefficient (translate f w) k=coefficient f k at hs
  have hm:=congrArg (fun c:ℂ=>character k w*c) hs
  simpa only [←mul_assoc,character_weight,one_mul] using hm
end EntireDoubleFourierTranslation318
