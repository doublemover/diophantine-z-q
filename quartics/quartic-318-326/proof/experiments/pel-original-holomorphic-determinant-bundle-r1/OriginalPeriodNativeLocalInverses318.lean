module
public import OriginalPeriodIndependentGraphs318
public import FiniteAnalyticCharts318
public section
noncomputable section
namespace OriginalPeriodNativeLocalInverses318
open OriginalComplexPeriodPair318 OriginalPeriodIndependentGraphs318
open OriginalPeriodProjectiveModel318 ComplexAffineFreeTranslation318 Filter
open scoped Topology
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

@[expose] def nativeX (z : ℂ) : ℂ := (pair L).weierstrassP z
@[expose] def nativeY (z : ℂ) : ℂ := (pair L).derivWeierstrassP z/2
lemma nativeX_analytic (z : ℂ) (hz : z∉(pair L).lattice) : AnalyticAt ℂ (nativeX L) z :=
  (pair L).analyticOnNhd_weierstrassP z hz
lemma nativeY_analytic (z : ℂ) (hz : z∉(pair L).lattice) : AnalyticAt ℂ (nativeY L) z := by
  have h := (pair L).analyticOnNhd_derivWeierstrassP z hz
  unfold nativeY
  fun_prop
lemma equation (z : ℂ) (hz : z∉(pair L).lattice) :
    finiteEquation L (nativeX L z,nativeY L z)=0 := by
  have h := (pair L).derivWeierstrassP_sq z hz
  dsimp [finiteEquation,nativeX,nativeY,A,B]
  linear_combination h/4

/-- Noncriticality of at least one ACTUAL native coordinate at every
finite original period point. This uses the original differential equation
and actual discriminant, not an injectivity-to-derivative shortcut. -/
theorem derivative_nonzero (z : ℂ) (hz : z∉(pair L).lattice) :
    deriv (nativeX L) z≠0 ∨ deriv (nativeY L) z≠0 := by
  have hx : deriv (nativeX L) z=2*nativeY L z := by
    rw [nativeX,(pair L).deriv_weierstrassP]
    dsimp [nativeY]
    ring
  have hy : deriv (nativeY L) z=3*(nativeX L z)^2+A L := by
    rw [nativeY,deriv_div_const,WeierstrassODE318.second_derivative (pair L) z hz]
    dsimp [nativeX,A]
    ring
  rcases finite_partial_nonzero L (nativeX L z,nativeY L z) (equation L z hz) with h | h
  · exact Or.inl (by rwa [hx])
  · exact Or.inr (by rw [hy]; exact neg_ne_zero.mp h)

/-- The original finite coordinates have actual holomorphic inverse
germs at EVERY nonlattice point, with both local inverse identities. -/
theorem finite_inverse (z : ℂ) (hz : z∉(pair L).lattice) :
    ∃ f g : ℂ → ℂ,(f=nativeX L ∨ f=nativeY L) ∧ AnalyticAt ℂ f z ∧
      AnalyticAt ℂ g (f z) ∧ g (f z)=z ∧
      (fun w => g (f w)) =ᶠ[𝓝 z] id ∧ (fun w => f (g w)) =ᶠ[𝓝 (f z)] id := by
  rcases derivative_nonzero L z hz with hx | hy
  · have hf := nativeX_analytic L z hz
    obtain ⟨g,hg,hval,hl,hr⟩ := FiniteAnalyticCharts318.analytic_inverse hf hx
    exact ⟨nativeX L,g,Or.inl rfl,hf,hg,hval,hl,hr⟩
  · have hf := nativeY_analytic L z hz
    obtain ⟨g,hg,hval,hl,hr⟩ := FiniteAnalyticCharts318.analytic_inverse hf hy
    exact ⟨nativeY L,g,Or.inr rfl,hf,hg,hval,hl,hr⟩

/-- At actual algebraic infinity the native U=X/Y coordinate has an
analytic inverse recovering the original lattice parameter; its second
coordinate is analytic in that same U coordinate. -/
theorem infinity_inverse : ∃ g : ℂ → ℂ,AnalyticAt ℂ g 0 ∧ g 0=0 ∧
    (fun z => g (2*WeierstrassInfinityChart318.u (pair L) z)) =ᶠ[𝓝 (0:ℂ)] id ∧
    (fun z => 2*WeierstrassInfinityChart318.u (pair L) (g z)) =ᶠ[𝓝 (0:ℂ)] id ∧
    AnalyticAt ℂ (fun z => 2*WeierstrassInfinityChart318.v (pair L) (g z)) 0 := by
  have hu : AnalyticAt ℂ (fun z => 2*WeierstrassInfinityChart318.u (pair L) z) 0 := by
    exact analyticAt_const.mul (WeierstrassInfinityChart318.u_analytic (pair L))
  have hd := OriginalPeriodNativeChartGerms318.native_infinity_derivative L
  have hval : 2*WeierstrassInfinityChart318.u (pair L) 0=0 := by
    simp [WeierstrassInfinityChart318.u_zero]
  obtain ⟨g,hg,hg0,hl,hr⟩ := FiniteAnalyticCharts318.analytic_inverse hu
    (by rw [hd.deriv]; norm_num)
  rw [hval] at hg hg0 hr
  refine ⟨g,hg,hg0,hl,hr,?_⟩
  have hv := WeierstrassInfinityChart318.v_analytic (pair L)
  have hvg : AnalyticAt ℂ (WeierstrassInfinityChart318.v (pair L)) (g 0) := by
    rw [hg0]
    exact hv
  exact analyticAt_const.mul (hvg.comp hg)
end OriginalPeriodNativeLocalInverses318
