module
public import CompactPeriodNormBound318
public import Mathlib.Analysis.Complex.Liouville
public section
noncomputable section
namespace CompactPeriodicHolomorphicQuotient318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
variable (L : AddSubgroup ComplexVectors) [DiscreteTopology L] [CompactSpace (Quotient L)]

/-- A nowhere-zero entire denominator makes a genuinely periodic
holomorphic quotient constant on the whole covering vector space. -/
theorem quotient_constant (f d : ComplexVectors → ℂ) (hf : Differentiable ℂ f)
    (hd : Differentiable ℂ d) (hden : ∀ z,d z≠0)
    (hp : ∀ (l : L) z,f (z+l.val)/d (z+l.val)=f z/d z) :
    ∃ c : ℂ,∀ z,f z=c*d z := by
  have he : Differentiable ℂ (fun z => f z/d z) := hf.div hd hden
  have hb := CompactPeriodNormBound318.bounded_range L (fun z => f z/d z)
    he.continuous (fun l z => congrArg norm (hp l z))
  refine ⟨f 0/d 0,?_⟩
  intro z
  exact (div_eq_iff (hden z)).mp (he.apply_eq_apply_of_bounded hb z 0)
end CompactPeriodicHolomorphicQuotient318
