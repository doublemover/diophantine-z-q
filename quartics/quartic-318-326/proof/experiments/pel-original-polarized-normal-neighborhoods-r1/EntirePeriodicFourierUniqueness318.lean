module
public import ActualDoubleFourierCoefficient318
public section
noncomputable section
namespace EntirePeriodicFourierUniqueness318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalThetaRealTorus318
open EntireIntegerPeriodicRealTorus318 EntireDoubleFourierTranslation318
open ActualDoubleFourierCoefficient318 UnitAddTorus MeasureTheory
local instance : MeasureSpace UnitAddCircle:=⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume:Measure UnitAddCircle):=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume:Measure UnitAddCircle):=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma frequency_surjective:Function.Surjective frequency:=by
  intro n
  refine ⟨(n 0,n 1),?_⟩
  ext i
  fin_cases i <;> rfl
lemma torus_zero(g:C(Torus,ℂ))(h:∀k:Index,mFourierCoeff g (frequency k)=0):g=0:=by
  have hz:∀n:Fin 2→ℤ,mFourierCoeff g n=0:=by
    intro n
    obtain ⟨k,rfl⟩:=frequency_surjective n
    exact h k
  have hs:Summable (mFourierCoeff g):=by
    simpa only [hz] using (summable_zero:Summable (fun _:Fin 2→ℤ=>(0:ℂ)))
  have hh:=hasSum_mFourier_series_of_summable hs
  simp only [hz,zero_smul] at hh
  exact hh.unique hasSum_zero
lemma zero_at_real_origin(f:ComplexVectors→ℂ)(hf:Continuous f)
    (h0:∀x y:ℂ,f ![x+1,y]=f ![x,y])
    (h1:∀x y:ℂ,f ![x,y+1]=f ![x,y])(hc:∀k,coefficient f k=0):f 0=0:=by
  have ht:torus f hf h0 h1=0:=torus_zero _ (fun k=>
    (coefficient_identification f hf h0 h1 k).trans (hc k))
  have he:=congrArg (fun g:C(Torus,ℂ)=>g (torusPoint (0:Fin 2→ℝ))) ht
  rw [EntireIntegerPeriodicRealTorus318.real_evaluation] at he
  simpa only [realPoint,Pi.zero_apply,Complex.ofReal_zero,ContinuousMap.zero_apply] using he

/-- Fourier coefficients determine the ENTIRE original periodic
function, not only its values almost everywhere on the real torus.
For each complex point, the actual contour shift identifies coefficients
of its translate; normalized Haar Fourier completeness gives its value. -/
theorem zero_of_coefficients(f:ComplexVectors→ℂ)(hf:Differentiable ℂ f)
    (h0:∀x y:ℂ,f ![x+1,y]=f ![x,y])
    (h1:∀x y:ℂ,f ![x,y+1]=f ![x,y])(hc:∀k,coefficient f k=0):f=0:=by
  funext w
  let g:=translate f w
  have hg:Differentiable ℂ g:=hf.comp (differentiable_id.add_const w)
  have hg0:∀x y:ℂ,g ![x+1,y]=g ![x,y]:=by
    intro x y
    have ha:![x+1,y]+w=![(x+w 0)+1,y+w 1]:=by
      ext i;fin_cases i <;> simp <;> ring
    have hb:![x,y]+w=![x+w 0,y+w 1]:=(coordinate_add x y w).symm
    simpa only [g,translate,ha,hb] using h0 (x+w 0) (y+w 1)
  have hg1:∀x y:ℂ,g ![x,y+1]=g ![x,y]:=by
    intro x y
    have ha:![x,y+1]+w=![x+w 0,(y+w 1)+1]:=by
      ext i;fin_cases i <;> simp <;> ring
    have hb:![x,y]+w=![x+w 0,y+w 1]:=(coordinate_add x y w).symm
    simpa only [g,translate,ha,hb] using h1 (x+w 0) (y+w 1)
  have hgc:∀k,coefficient g k=0:=by
    intro k
    rw [coefficient_translation f hf h0 h1,hc,mul_zero]
  have hv:=zero_at_real_origin g hg.continuous hg0 hg1 hgc
  simpa only [g,translate,zero_add,Pi.zero_apply] using hv
end EntirePeriodicFourierUniqueness318
