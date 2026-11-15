module
public import PELOriginalPolarizationTransitions318
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public section
noncomputable section
namespace PELOriginalPolarizationLineBundle318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationAutomorphy318 PELOriginalPolarizationTransitions318
open PELOriginalHermitianForm318 Filter Topology
variable (τ:ℂ) (hτ:0<τ.im)

/-- A genuine complex line bundle over the ORIGINAL compact period
surface. Gluing uses the actual original local covering lifts and the
constructed factors, not a pre-existing arbitrary line-bundle hypothesis. -/
@[expose] def core:VectorBundleCore ℂ (Base τ) ℂ ComplexVectors := by
  letI : DiscreteTopology (P τ) := PELOriginalPeriodLattice318.original_discrete τ hτ
  exact {
    baseSet:=baseSet τ hτ
    isOpen_baseSet a:=(chart τ hτ a).open_source
    indexAt q:=(quotient_surjective (P τ) q).choose
    mem_baseSet_at q:=by
      have h:=localChart_center (P τ) ((quotient_surjective (P τ) q).choose)
      simpa only [baseSet,chart,(quotient_surjective (P τ) q).choose_spec] using h
    coordChange a b q:=transition τ hτ a b q • ContinuousLinearMap.id ℂ ℂ
    coordChange_self a q _ v:=by simp [transition_self]
    continuousOn_coordChange a b:=
      (transition_continuous τ hτ a b).smul continuousOn_const
    coordChange_comp a b c q hq v:=by
      simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
      rw [←mul_assoc,transition_comp τ hτ a b c q hq.1.1 hq.1.2 hq.2]
  }

abbrev Fiber (q:Base τ):Type:=(core τ hτ).Fiber q
abbrev Total:Type:=(core τ hτ).TotalSpace
instance fiberBundle: FiberBundle ℂ (Fiber τ hτ):=(core τ hτ).fiberBundle
instance vectorBundle:VectorBundle ℂ ℂ (Fiber τ hτ):=(core τ hτ).vectorBundle
lemma rank_one (q:Base τ):Module.finrank ℂ (Fiber τ hτ q)=1:=by
  change Module.finrank ℂ ℂ=1
  exact Module.finrank_self ℂ
lemma original_local_transition (a b:ComplexVectors) (q:Base τ):
    (core τ hτ).coordChange a b q=
      factor τ hτ (shift τ hτ a b q) (chart τ hτ a q) • ContinuousLinearMap.id ℂ ℂ:=rfl
lemma projection_continuous:Continuous (core τ hτ).proj:=(core τ hτ).continuous_proj

lemma factor_analytic (l:L τ hτ) (z:ComplexVectors):
    AnalyticAt ℂ (factor τ hτ l) z:=by
  have h:AnalyticAt ℂ (fun w:ComplexVectors=>form τ hτ w l.val) z:=
    (continuousLinear τ hτ l.val).analyticAt z
  have he:AnalyticAt ℂ Complex.exp (exponent τ hτ l z):=by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.exp_analytic _
  exact he.comp ((analyticAt_const.mul (h.add analyticAt_const)).add analyticAt_const)

/-- The actual bundle transition coefficients are holomorphic in the
ORIGINAL quotient surface's local complex coordinates. The difference
of the covering lifts is proved locally constant in the true lattice. -/
lemma transition_analytic (a b z:ComplexVectors)
    (ha:z∈(chart τ hτ a).target)
    (hb:projection (P τ) z∈baseSet τ hτ b):
    AnalyticAt ℂ (fun w=>transition τ hτ a b (projection (P τ) w)) z:=by
  letI : DiscreteTopology (P τ) := PELOriginalPeriodLattice318.original_discrete τ hτ
  have hq:projection (P τ) z∈baseSet τ hτ a:=by
    change projection (P τ) z∈(chart τ hτ a).source
    have h:=(chart τ hτ a).map_target ha
    simpa only [chart,localChart_symm] using h
  have hs:=shift_locally_constant τ hτ a b (projection (P τ) z) hq hb
  have hp:Continuous (projection (P τ)):=QuotientAddGroup.continuous_mk
  have hs' : ∀ᶠ w in 𝓝 z, shift τ hτ a b (projection (P τ) w) =
      shift τ hτ a b (projection (P τ) z) := Filter.Tendsto.eventually hp.continuousAt hs
  apply (factor_analytic τ hτ (shift τ hτ a b (projection (P τ) z)) z).congr
  filter_upwards [hs',(chart τ hτ a).open_target.mem_nhds ha]
    with w hw hwa
  have he:chart τ hτ a (projection (P τ) w)=w:=by
    have h:=(chart τ hτ a).right_inv hwa
    simpa only [chart,localChart_symm] using h
  simp only [transition,hw,he]
end PELOriginalPolarizationLineBundle318
