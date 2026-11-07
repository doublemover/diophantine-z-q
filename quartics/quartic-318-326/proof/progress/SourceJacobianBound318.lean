module
public import CuspArakelovData318
public import SourceFiniteDivisor318
public section
noncomputable section
namespace SourceJacobianBound318
open NumberField Matrix CuspArakelovData318
set_option maxHeartbeats 0

/-- Explicit finite intersection data. The actual regular-model interpretation,
local different theorem and projection formula are visible fields. -/
structure FiniteData (ι κ:Type*) [Fintype ι] [DecidableEq ι] [Fintype κ]
    (n d N:ℕ) where
  matrix:Matrix ι ι ℝ
  negative_definite:(-matrix).PosDef
  off_diagonal:∀i j,i≠j → 0≤matrix i j
  outside_matrix:Matrix ι κ ℝ
  outside_nonneg:∀i j,0≤outside_matrix i j
  pullbackExceptional:ι→ℝ
  canonicalExceptional:ι→ℝ
  pullbackOutside:κ→ℝ
  canonicalOutside:κ→ℝ
  local_domination:∀j,canonicalOutside j≤pullbackOutside j
  adjunction:∀i,(matrix *ᵥ (pullbackExceptional-canonicalExceptional)) i+
    (outside_matrix *ᵥ (pullbackOutside-canonicalOutside)) i≤0
  sectionExceptional:ι→ℝ
  sectionOutside:κ→ℝ
  sectionExceptional_nonneg:∀i,0≤sectionExceptional i
  sectionOutside_nonneg:∀j,0≤sectionOutside j
  pullback_section:(∑i,pullbackExceptional i*sectionExceptional i)+
    (∑j,pullbackOutside j*sectionOutside j)≤
      FiniteDivisorArithmetic318.horizontalContact (1/(n:ℚ))+
      2*(∑p∈(6*N).primeFactors,(⌊Real.log (d:ℝ)/Real.log (p:ℝ)⌋₊:ℝ)*Real.log p)

@[expose] def FiniteData.intersection {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {n d N:ℕ} (F:FiniteData ι κ n d N) : ℝ :=
  (∑i,F.canonicalExceptional i*F.sectionExceptional i)+
    (∑j,F.canonicalOutside j*F.sectionOutside j)

theorem FiniteData.bound {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {n d N:ℕ} (F:FiniteData ι κ n d N) (hn:2≤n) (hd:1≤d) (hN:1≤N) :
    F.intersection≤3*absLogHeight₁ (1/(n:ℚ))+
      2*Real.log (6*(N:ℝ))*Real.log d/Real.log 2 := by
  exact SourceFiniteDivisor318.canonical_section_bound F.matrix F.negative_definite
    F.off_diagonal F.outside_matrix F.outside_nonneg F.pullbackExceptional
    F.canonicalExceptional F.pullbackOutside F.canonicalOutside F.local_domination
    F.adjunction F.sectionExceptional F.sectionOutside F.sectionExceptional_nonneg
    F.sectionOutside_nonneg n d N hn hd hN F.pullback_section

/-- All logarithms in the final budget are the source's actual logarithms. -/
theorem logarithmic_parameters (g d N:ℕ) (hg:2≤g) (hgd:g≤d) (hN:1≤N) :
    1≤Real.log (6*(d:ℝ)*N) ∧
    0≤Real.log (6*(N:ℝ)) ∧ 0≤Real.log (d:ℝ) ∧
    Real.log (6*(N:ℝ))≤Real.log (6*(d:ℝ)*N) ∧
    Real.log (d:ℝ)≤Real.log (6*(d:ℝ)*N) ∧
    Real.log ((g:ℝ)+1)≤Real.log (6*(d:ℝ)*N) ∧
    100*(g:ℝ)^2*Real.log (2*g*N)≤100*(d:ℝ)^2*Real.log (6*d*N) := by
  have hgR : (2:ℝ)≤g := by exact_mod_cast hg
  have hgdR : (g:ℝ)≤d := by exact_mod_cast hgd
  have hNR : (1:ℝ)≤N := by exact_mod_cast hN
  have hdR : (2:ℝ)≤d := hgR.trans hgdR
  have hmul : (d:ℝ)≤d*N := by nlinarith
  have hmul' : (g:ℝ)≤g*N := by nlinarith
  have hbig : (3:ℝ)≤6*d*N := by nlinarith
  have hlog3 := Real.log_le_log (by norm_num : (0:ℝ)<3) hbig
  have hL : 1≤Real.log (6*(d:ℝ)*N) := by linarith [Real.log_three_gt_d9]
  have hA : 0≤Real.log (6*(N:ℝ)) := Real.log_nonneg (by linarith)
  have hB : 0≤Real.log (d:ℝ) := Real.log_nonneg (by linarith)
  have hAL : Real.log (6*(N:ℝ))≤Real.log (6*(d:ℝ)*N) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hBL : Real.log (d:ℝ)≤Real.log (6*(d:ℝ)*N) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hgL : Real.log ((g:ℝ)+1)≤Real.log (6*(d:ℝ)*N) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hwL : Real.log (2*(g:ℝ)*N)≤Real.log (6*(d:ℝ)*N) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hw0 : 0≤Real.log (2*(g:ℝ)*N) := Real.log_nonneg (by nlinarith)
  have hg2 : (g:ℝ)^2≤(d:ℝ)^2 := by nlinarith
  have hw : 100*(g:ℝ)^2*Real.log (2*g*N)≤100*(d:ℝ)^2*Real.log (6*d*N) := by
    apply mul_le_mul (by nlinarith : 100*(g:ℝ)^2≤100*(d:ℝ)^2) hwL hw0
    positivity
  exact ⟨hL,hA,hB,hAL,hBL,hgL,hw⟩

/-- End-to-end quadratic-log Jacobian bound from actual cusp functions,
actual disc energies, finite divisor data, and the three named Arakelov
identifications. No final differential, Wronskian, finite-place or Jacobian
height bound is supplied as a premise. -/
theorem jacobian_GR_bound (K:Type*) [Field K] [NumberField K]
    {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (g i d N:ℕ) (hg:2≤g) (hi:i≤g^3+1) (hgd:g≤d) (hN:1≤N)
    (D:CuspArakelovData318.Data K g i N) (F:FiniteData ι κ (2^128+i) d N)
    (pointHeight hFal hGR:ℝ) (metricLog:(K→+*ℂ)→ℝ)
    (minimal_model:pointHeight≤F.intersection-
      embeddingAverage K (fun sigma=>D.differentialLog sigma+metricLog sigma))
    (faltings_wronskian:hFal≤(g:ℝ)*(g+1)/2*pointHeight+
      embeddingAverage K (fun sigma=>D.wronskianLog sigma+(g:ℝ)*(g+1)/2*metricLog sigma))
    (GR_normalization:hGR=hFal+(g:ℝ)*Real.log (Real.sqrt Real.pi)) :
    hGR≤2^11*(d:ℝ)^2*(Real.log (6*d*N))^2 := by
  have hgR : (1:ℝ)≤g := by exact_mod_cast (show 1≤g by omega)
  have hgdR : (g:ℝ)≤d := by exact_mod_cast hgd
  have hk : 0≤(g:ℝ)*(g+1)/2 := by positivity
  have hcancel := MetricCancellation318.exact_metric_cancellation Finset.univ
    (Module.finrank ℚ K) ((g:ℝ)*(g+1)/2) F.intersection pointHeight hFal
    D.differentialLog metricLog D.wronskianLog hk minimal_model faltings_wronskian
  change hFal≤(g:ℝ)*(g+1)/2*F.intersection-
    (g:ℝ)*(g+1)/2*embeddingAverage K D.differentialLog+
    embeddingAverage K D.wronskianLog at hcancel
  obtain ⟨hdelta,hW⟩ := CuspArakelovData318.actual_archimedean_bounds D hg hi hN
  obtain ⟨hL,hA,hB,hAL,hBL,hgL,hwL⟩ := logarithmic_parameters g d N hg hgd hN
  have hha := CuspHeight318.candidate_height g i hg hi
  have hF:=F.bound (by omega) (by omega) hN
  have hF' : F.intersection≤3*absLogHeight₁ (1/((2:ℚ)^128+i))+
      2*Real.log (6*(N:ℝ))*Real.log d/Real.log 2 := by
    convert hF using 1 <;> norm_num
  have hGRb : hGR≤hFal+(g:ℝ) := by
    rw [GR_normalization]
    exact MetricCancellation318.normalization_shift g hFal (by positivity)
  apply MetricCancellation318.jacobian_GR_budget g d (Real.log (6*(d:ℝ)*N))
    (Real.log (6*(N:ℝ))) (Real.log (d:ℝ))
    (absLogHeight₁ (1/((2:ℚ)^128+i))) F.intersection
    (-embeddingAverage K D.differentialLog) (embeddingAverage K D.wronskianLog) hFal hGR
    hgR hgdR hL hA hB hAL hBL (by linarith) hF' hdelta (hW.trans hwL) _ hGRb
  linarith

end SourceJacobianBound318
#print axioms SourceJacobianBound318.FiniteData.bound
#print axioms SourceJacobianBound318.logarithmic_parameters
#print axioms SourceJacobianBound318.jacobian_GR_bound
