module
public import PELOriginalThetaConvergence318
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public section
noncomputable section
namespace PELOriginalThetaRealTorus318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318
open MeasureTheory UnitAddTorus
open scoped ComplexConjugate
variable (τ:ℂ) (hτ:0<τ.im)
abbrev Torus:=UnitAddTorus (Fin 2)
local instance : MeasureSpace UnitAddCircle:=⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume:Measure UnitAddCircle):=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume:Measure UnitAddCircle):=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
@[expose] def frequency (n:Index):Fin 2→ℤ:=![n.1,n.2]
lemma frequency_eq_zero (n:Index):frequency n=0↔n=0:=by
  constructor
  · intro h
    apply Prod.ext
    · exact congrFun h 0
    · exact congrFun h 1
  · rintro rfl;ext i;fin_cases i <;> rfl
@[expose] def coefficient (n:Index):ℂ:=term τ n 0
@[expose] def torusTerm (n:Index):C(Torus,ℂ):=
  coefficient τ n • mFourier (frequency n)
lemma torusTerm_norm (n:Index):‖torusTerm τ n‖=‖coefficient τ n‖:=by
  rw [torusTerm,norm_smul,mFourier_norm,mul_one]
lemma torusTerm_summable:Summable (torusTerm τ):=by
  apply (bound_summable τ hτ 0).of_norm_bounded
  intro n
  rw [torusTerm_norm]
  exact norm_bound τ hτ 0 0 (by simp) (by simp) n

/-- The FULL original theta series restricted to the real unit torus,
constructed as a convergent series in the Banach space of continuous maps.
This supplies genuine uniform summation before taking a Fourier coefficient. -/
@[expose] def torusTheta:C(Torus,ℂ):=∑'n:Index,torusTerm τ n
lemma torus_hasSum:HasSum (torusTerm τ) (torusTheta τ):=
  (torusTerm_summable τ hτ).hasSum

@[expose] def realPoint (x:Fin 2→ℝ):ComplexVectors:=fun j=>(x j:ℂ)
@[expose] def torusPoint (x:Fin 2→ℝ):Torus:=fun j=>(x j:UnitAddCircle)
lemma term_real (n:Index) (x:Fin 2→ℝ):
    torusTerm τ n (torusPoint x)=term τ n (realPoint x):=by
  simp only [torusTerm,ContinuousMap.smul_apply,smul_eq_mul,coefficient,
    mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two,frequency,Matrix.cons_val_zero,
    Matrix.cons_val_one,torusPoint,AddCircle.fourier_coe_apply,Complex.ofReal_one,div_one]
  simp only [term,linear,Pi.zero_apply,mul_zero,add_zero,Complex.exp_zero]
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [realPoint]
  ring

/-- Evaluation agrees with the actual original entire theta, not a
separately chosen periodic function or formal Fourier series. -/
lemma real_evaluation (x:Fin 2→ℝ):
    torusTheta τ (torusPoint x)=theta τ (realPoint x):=by
  have h:HasSum (fun n:Index=>torusTerm τ n (torusPoint x))
      (torusTheta τ (torusPoint x)):=
    (ContinuousMap.evalCLM ℂ (torusPoint x)).hasSum (torus_hasSum τ hτ)
  simp only [term_real] at h
  exact h.unique (PELOriginalThetaConvergence318.hasSum τ hτ (realPoint x))

/-- Every point of the real torus has a genuine real representative. -/
lemma torusPoint_surjective:Function.Surjective torusPoint:=by
  intro q
  choose x hx using fun j:Fin 2=>Quotient.exists_rep (q j)
  exact ⟨x,funext hx⟩
end PELOriginalThetaRealTorus318
