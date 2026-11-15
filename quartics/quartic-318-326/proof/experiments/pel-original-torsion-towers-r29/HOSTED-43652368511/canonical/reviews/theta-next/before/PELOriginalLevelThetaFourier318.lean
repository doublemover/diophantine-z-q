module
public import PELOriginalLevelTheta318
public import PELOriginalThetaRealTorus318
public section
noncomputable section
namespace PELOriginalLevelThetaFourier318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318
open PELOriginalThetaRealTorus318 PELOriginalLevelTheta318 UnitAddTorus MeasureTheory
variable (τ:ℂ) (hτ:0<τ.im) (N:ℕ) [NeZero N]
local instance : MeasureSpace UnitAddCircle:=⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume:Measure UnitAddCircle):=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume:Measure UnitAddCircle):=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

@[expose] def coefficient (r:Label N) (k:Index):ℂ:=levelTerm τ N r k 0
@[expose] def torusTerm (r:Label N) (k:Index):C(Torus,ℂ):=
  coefficient τ N r k • mFourier (frequency k)
lemma torusTerm_summable (r:Label N):Summable (torusTerm τ N r):=by
  apply (PELOriginalScaledThetaConvergence318.bound_summable τ hτ
    (1/(N:ℝ)) (inverse_level_positive N) 0).of_norm_bounded
  intro k
  rw [torusTerm,norm_smul,mFourier_norm,mul_one]
  by_cases hk:accepts N r k
  · simpa only [coefficient,levelTerm,PELOriginalScaledThetaHolomorphy318.selectedTerm,if_pos hk] using
      PELOriginalScaledThetaConvergence318.norm_bound τ hτ (1/(N:ℝ))
        (inverse_level_positive N) 0 0 (by simp) (by simp) k
  · simp only [coefficient,levelTerm,PELOriginalScaledThetaHolomorphy318.selectedTerm,if_neg hk,norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
@[expose] def torusTheta (r:Label N):C(Torus,ℂ):=∑'k:Index,torusTerm τ N r k
lemma scaled_real_term (k:Index) (x:Fin 2→ℝ):
    PELOriginalScaledThetaConvergence318.term τ (1/(N:ℝ)) k 0*
      mFourier (frequency k) (torusPoint x)=
        PELOriginalScaledThetaConvergence318.term τ (1/(N:ℝ)) k (realPoint x):=by
  simp only [mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two,frequency,
    Matrix.cons_val_zero,Matrix.cons_val_one,torusPoint,AddCircle.fourier_coe_apply,
    Complex.ofReal_one,div_one,PELOriginalScaledThetaConvergence318.term,linear,
    Pi.zero_apply,mul_zero,add_zero,Complex.exp_zero]
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [realPoint]
  ring
lemma term_real (r:Label N) (k:Index) (x:Fin 2→ℝ):
    torusTerm τ N r k (torusPoint x)=levelTerm τ N r k (realPoint x):=by
  by_cases hk:accepts N r k
  · simpa only [torusTerm,ContinuousMap.smul_apply,smul_eq_mul,coefficient,levelTerm,
      PELOriginalScaledThetaHolomorphy318.selectedTerm,if_pos hk] using scaled_real_term τ N k x
  · simp [torusTerm,coefficient,levelTerm,PELOriginalScaledThetaHolomorphy318.selectedTerm,hk]
lemma real_evaluation (r:Label N) (x:Fin 2→ℝ):
    torusTheta τ N r (torusPoint x)=levelTheta τ N r (realPoint x):=by
  have h:HasSum (fun k:Index=>torusTerm τ N r k (torusPoint x))
      (torusTheta τ N r (torusPoint x)):=
    (ContinuousMap.evalCLM ℂ (torusPoint x)).hasSum (torusTerm_summable τ hτ N r).hasSum
  simp only [term_real] at h
  exact h.unique (PELOriginalLevelTheta318.summable τ hτ N r (realPoint x)).hasSum
lemma frequency_injective:Function.Injective frequency:=by
  intro k j h
  exact Prod.ext (congrFun h 0) (congrFun h 1)
@[expose] def fourierCoefficient (k:Index):C(Torus,ℂ)→L[ℂ]ℂ:=
  (innerSL ℂ (mFourierLp 2 (frequency k))).comp
    (ContinuousMap.toLp (E:=ℂ) 2 (volume:Measure Torus) ℂ)
lemma fourier_monomial (k j:Index):
    fourierCoefficient k (mFourier (frequency j))=if j=k then 1 else 0:=by
  have h:=(orthonormal_iff_ite.mp (orthonormal_mFourier (d:=Fin 2))) (frequency k) (frequency j)
  change inner ℂ (mFourierLp 2 (frequency k)) (mFourierLp 2 (frequency j))=_
  rw [h]
  by_cases hj:j=k
  · subst j;simp
  · have hn:frequency k≠frequency j:=fun he=>hj (frequency_injective he).symm
    simp only [if_neg hn,if_neg hj]
lemma fourier_term (r:Label N) (k j:Index):
    fourierCoefficient k (torusTerm τ N r j)=if j=k then coefficient τ N r k else 0:=by
  rw [torusTerm,map_smul,fourier_monomial]
  split_ifs with h
  · subst j;simp
  · simp

/-- Every Fourier coefficient of EVERY actual characteristic subseries
is computed by a continuous functional on its proved Banach-space sum. -/
theorem fourier_exact (r:Label N) (k:Index):
    fourierCoefficient k (torusTheta τ N r)=coefficient τ N r k:=by
  have h:HasSum (fun j:Index=>fourierCoefficient k (torusTerm τ N r j))
      (fourierCoefficient k (torusTheta τ N r)):=
    (fourierCoefficient k).hasSum (torusTerm_summable τ hτ N r).hasSum
  simp only [fourier_term] at h
  exact h.unique (hasSum_ite_eq k (coefficient τ N r k))
end PELOriginalLevelThetaFourier318
