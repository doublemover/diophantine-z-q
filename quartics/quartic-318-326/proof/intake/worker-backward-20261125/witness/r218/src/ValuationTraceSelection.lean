module
public import ValuationNormChainExtraction
public section
namespace ValuationTraceSelection
variable {K : Type*} [Field K]

/-- The source trace/norm equation supplies the trace inequality and valuation
identity before selecting one common place. The pole threshold is explicit. -/
theorem one_place (v : AddValuation K (WithTop ℤ)) (w conjugateW n : K)
    (R a b c : ℤ) (hw : v w=a) (hb : v conjugateW=b) (hn : v n=c)
    (heq : n*(w+conjugateW)=w*conjugateW)
    (hpole : 0<2*c+R) : 0<2*a+R ∨ 0<2*b+R := by
  have hw0 : w≠0 := (v.ne_top_iff).mp (by rw [hw]; simp)
  have hb0 : conjugateW≠0 := (v.ne_top_iff).mp (by rw [hb]; simp)
  have ht0 : w+conjugateW≠0 := by
    intro hz
    rw [hz,mul_zero] at heq
    exact mul_ne_zero hw0 hb0 heq.symm
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr ht0)
  have hid := congrArg v heq
  rw [v.map_mul,v.map_mul,hw,hb,hn,←ht] at hid
  have hct : c+t=a+b := by exact_mod_cast hid
  have hmin := v.map_add w conjugateW
  rw [hw,hb,←ht] at hmin
  have hmin' : min a b≤t := by exact_mod_cast hmin
  apply NormChainValuation.reciprocal_trace_one_place R a b t hmin'
  omega

end ValuationTraceSelection
