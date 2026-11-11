module
public import EntireIntegerPeriodicRealTorus318
public import PELOriginalLevelThetaFourier318
public section
noncomputable section
namespace ActualDoubleFourierCoefficient318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalThetaRealTorus318
open EntireIntegerPeriodicRealTorus318 EntireDoubleFourierTranslation318
open EntirePeriodicDoubleIntegral318 UnitAddTorus MeasureTheory
local instance : MeasureSpace UnitAddCircle:=⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume:Measure UnitAddCircle):=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume:Measure UnitAddCircle):=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma circle_integral(g:UnitAddCircle→ℂ):
    (∫q:UnitAddCircle,g q)=∫x:ℝ in 0..1,g (x:UnitAddCircle):=by
  simpa [AddCircle.haarAddCircle] using
    (AddCircle.intervalIntegral_preimage (1:ℝ) 0 g).symm
/-- Actual normalized Haar integral equals the two genuine unit-period
integrals, with its order fixed to the coefficient definition. -/
lemma torus_integral(g:C(Torus,ℂ)):
    (∫q:Torus,g q)=∫y:ℝ in 0..1,∫x:ℝ in 0..1,
      g ![(x:UnitAddCircle),(y:UnitAddCircle)]:=by
  let G:UnitAddCircle×UnitAddCircle→ℂ:=fun p=>g ![p.1,p.2]
  have hc:Continuous G:=by
    apply g.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    · exact continuous_fst
    · exact continuous_snd
  have hi:Integrable G:=by
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_isCompact isCompact_univ
  have he:(∫q:Torus,g q)=∫p:UnitAddCircle×UnitAddCircle,G p:=by
    simpa only [G,MeasurableEquiv.finTwoArrow_symm_apply] using
      ((MeasureTheory.volume_preserving_finTwoArrow UnitAddCircle).symm.integral_comp' g).symm
  rw [he,MeasureTheory.integral_prod_symm G hi]
  simp_rw [circle_integral]

lemma character_real(k:Index)(x:Fin 2→ℝ):
    mFourier (-frequency k) (torusPoint x)=weight k (realPoint x):=by
  simp only [mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two,frequency,
    Pi.neg_apply,Matrix.cons_val_zero,Matrix.cons_val_one,torusPoint,
    AddCircle.fourier_coe_apply,Complex.ofReal_one,div_one,weight,linear,realPoint]
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The coefficient used in the genuine holomorphic contour argument
is exactly the normalized real-torus Fourier coefficient of the actual
periodic descent, not a competing normalization or formal series label. -/
theorem coefficient_identification(f:ComplexVectors→ℂ)(hf:Continuous f)
    (h0:∀x y:ℂ,f ![x+1,y]=f ![x,y])
    (h1:∀x y:ℂ,f ![x,y+1]=f ![x,y])(k:Index):
    mFourierCoeff (torus f hf h0 h1) (frequency k)=coefficient f k:=by
  let g:C(Torus,ℂ):=mFourier (-frequency k)*(torus f hf h0 h1)
  change (∫q:Torus,g q)=_
  rw [torus_integral]
  change (∫y:ℝ in 0..1,∫x:ℝ in 0..1,
    mFourier (-frequency k) ![(x:UnitAddCircle),(y:UnitAddCircle)]*
      torus f hf h0 h1 ![(x:UnitAddCircle),(y:UnitAddCircle)])=_
  have he(x y:ℝ):
      mFourier (-frequency k) ![(x:UnitAddCircle),(y:UnitAddCircle)]*
        torus f hf h0 h1 ![(x:UnitAddCircle),(y:UnitAddCircle)]=
      f ![(x:ℂ),(y:ℂ)]*weight k ![(x:ℂ),(y:ℂ)]:=by
    have hm:=character_real k ![x,y]
    have hf':=EntireIntegerPeriodicRealTorus318.real_evaluation f hf h0 h1 ![x,y]
    simpa only [torusPoint,realPoint,Matrix.cons_val_zero,Matrix.cons_val_one,mul_comm] using
      congrArg₂ (fun a b:ℂ=>a*b) hm hf'
  simp_rw [he]
  simp only [coefficient,periodIntegral,weighted,Pi.zero_apply,add_zero]
lemma functional_identification(k:Index)(g:C(Torus,ℂ)):
    PELOriginalLevelThetaFourier318.fourierCoefficient k g=
      mFourierCoeff g (frequency k):=by
  change inner ℂ (mFourierLp 2 (frequency k)) (ContinuousMap.toLp 2 volume ℂ g)=_
  simp only [mFourierLp,ContinuousMap.inner_toLp,mFourierCoeff,←mFourier_neg,
    smul_eq_mul,mul_comm]
lemma functional_coefficient(f:ComplexVectors→ℂ)(hf:Continuous f)
    (h0:∀x y:ℂ,f ![x+1,y]=f ![x,y])
    (h1:∀x y:ℂ,f ![x,y+1]=f ![x,y])(k:Index):
    PELOriginalLevelThetaFourier318.fourierCoefficient k (torus f hf h0 h1)=
      coefficient f k:=by
  rw [functional_identification,coefficient_identification]
end ActualDoubleFourierCoefficient318
