module
public import AnalyticNonzeroSquareRoot318
public import Mathlib.Topology.Connected.TotallyDisconnected
public section
noncomputable section
namespace ConnectedSquareRootComparison318
open Set

/-- Two continuous nonvanishing square roots on a connected domain differ
by ONE constant sign on the whole domain. No pointwise sign choices enter. -/
theorem exists_sign {U:Set ℂ} (hU:IsPreconnected U) (hn:U.Nonempty)
    {f g:ℂ→ℂ} (hf:ContinuousOn f U) (hg:ContinuousOn g U)
    (he:∀z∈U,f z^2=g z^2) (hg0:∀z∈U,g z≠0) :
    ∃s:ℂ,s^2=1 ∧ ∀z∈U,f z=s*g z := by
  let r:ℂ→ℂ:=fun z=>f z/g z
  have hr:ContinuousOn r U:=hf.div hg hg0
  have hs:∀z∈U,r z^2=1:=by
    intro z hz
    dsimp [r]
    rw [div_pow,he z hz,div_self (pow_ne_zero 2 (hg0 z hz))]
  have hm:MapsTo r U ({1,-1}:Set ℂ):=by
    intro z hz
    have hh:r z^2=(1:ℂ)^2:=by simpa using hs z hz
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with h|h <;> simp [h]
  have hd:IsDiscrete ({1,-1}:Set ℂ):=by
    letI:Fintype ↥({1,-1}:Set ℂ):=((Set.finite_singleton (-1:ℂ)).insert 1).fintype
    rw [isDiscrete_iff_discreteTopology]
    infer_instance
  obtain ⟨a,ha⟩:=hn
  refine ⟨r a,hs a ha,?_⟩
  intro z hz
  have hconst:r z=r a:=hU.constant_of_mapsTo hd hr hm hz ha
  calc
    f z=r z*g z := (div_mul_cancel₀ (f z) (hg0 z hz)).symm
    _=r a*g z := by rw [hconst]
end ConnectedSquareRootComparison318
