module
public import PELOriginalThetaRealTorus318
public section
noncomputable section
namespace PELOriginalThetaConstantCoefficient318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318
open PELOriginalThetaRealTorus318 UnitAddTorus MeasureTheory
variable (τ:ℂ) (hτ:0<τ.im)
local instance : MeasureSpace UnitAddCircle:=⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume:Measure UnitAddCircle):=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume:Measure UnitAddCircle):=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Actual normalized zero Fourier coefficient. The continuous-map-to-L²
map and the inner product with the constant monomial are continuous linear,
so evaluation on the convergent FULL series is justified. -/
@[expose] def average:C(Torus,ℂ)→L[ℂ]ℂ:=
  (innerSL ℂ (mFourierLp 2 (0:Fin 2→ℤ))).comp
    (ContinuousMap.toLp (E:=ℂ) 2 (volume:Measure Torus) ℂ)
lemma average_monomial (n:Index):
    average (mFourier (frequency n))=if n=0 then 1 else 0:=by
  have h:=(orthonormal_iff_ite.mp (orthonormal_mFourier (d:=Fin 2)))
    (0:Fin 2→ℤ) (frequency n)
  change inner ℂ (mFourierLp 2 (0:Fin 2→ℤ))
    (mFourierLp 2 (frequency n))=if n=0 then 1 else 0
  rw [h]
  by_cases hn:n=0
  · subst n;simp [frequency]
  · have hf:(0:Fin 2→ℤ)≠frequency n:=fun he=>hn ((frequency_eq_zero n).mp he.symm)
    simp only [if_neg hf,if_neg hn]
lemma average_term (n:Index):average (torusTerm τ n)=if n=0 then 1 else 0:=by
  rw [torusTerm,map_smul,average_monomial]
  split_ifs with hn
  · subst n
    simp [coefficient,term,quadratic,linear]
  · simp

/-- Exact constant Fourier coefficient ONE for the actual original theta.
No assumed nonzero theta constant, positivity of individual complex terms,
or cancellation-free evaluation at the origin is used. -/
theorem constant_coefficient:average (torusTheta τ)=1:=by
  have h:HasSum (fun n:Index=>average (torusTerm τ n))
      (average (torusTheta τ)):=average.hasSum (torus_hasSum τ hτ)
  have h0:HasSum (fun n:Index=>if n=0 then (1:ℂ) else 0) 1:=by
    simpa using (hasSum_ite_eq (0:Index) (1:ℂ))
  simp only [average_term] at h
  exact h.unique h0
lemma torusTheta_ne_zero:torusTheta τ≠0:=by
  intro h
  have hc:=constant_coefficient τ hτ
  rw [h,map_zero] at hc
  exact zero_ne_one hc

/-- There is an ACTUAL real covering point where the original theta
series is nonzero. This proves nontriviality, not nonvanishing everywhere. -/
theorem exists_real_nonzero:∃x:Fin 2→ℝ,theta τ (realPoint x)≠0:=by
  by_contra h
  push_neg at h
  apply torusTheta_ne_zero τ hτ
  ext q
  obtain ⟨x,rfl⟩:=torusPoint_surjective q
  exact (real_evaluation τ hτ x).trans (h x)
theorem exists_nonzero:∃z:ComplexVectors,theta τ z≠0:=by
  obtain ⟨x,hx⟩:=exists_real_nonzero τ hτ
  exact ⟨realPoint x,hx⟩
end PELOriginalThetaConstantCoefficient318
