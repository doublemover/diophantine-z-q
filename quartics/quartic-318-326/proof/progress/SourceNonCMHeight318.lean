module
public import SourceJacobianBound318
public import IsogenyHeightTransfer318
public section
noncomputable section
namespace SourceNonCMHeight318
open NumberField SourceJacobianBound318 CuspArakelovData318 ActualLogWeight318
set_option maxHeartbeats 0

/-- The exact named global identities remain visible instead of a supplied
Jacobian-height estimate. Their source interpretation is independently audited. -/
structure ArakelovIdentifications (K:Type*) [Field K] [NumberField K]
    {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {g i d N:ℕ} (D:CuspArakelovData318.Data K g i N)
    (F:FiniteData ι κ (2^128+i) d N) where
  pointHeight:ℝ
  hFal:ℝ
  hGR:ℝ
  metricLog:(K→+*ℂ)→ℝ
  minimal_model:pointHeight≤F.intersection-
    embeddingAverage K (fun sigma=>D.differentialLog sigma+metricLog sigma)
  faltings_wronskian:hFal≤(g:ℝ)*(g+1)/2*pointHeight+
    embeddingAverage K (fun sigma=>D.wronskianLog sigma+(g:ℝ)*(g+1)/2*metricLog sigma)
  GR_normalization:hGR=hFal+(g:ℝ)*Real.log (Real.sqrt Real.pi)

theorem jacobian_quadratic (K:Type*) [Field K] [NumberField K]
    {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {g i d N:ℕ} (D:CuspArakelovData318.Data K g i N)
    (F:FiniteData ι κ (2^128+i) d N) (A:ArakelovIdentifications K D F)
    (hg:2≤g) (hi:i≤g^3+1) (hgd:g≤d) (hN:1≤N) :
    A.hGR≤2^11*(d:ℝ)^2*(Real.log (6*d*N))^2 :=
  SourceJacobianBound318.jacobian_GR_bound K g i d N hg hi hgd hN D F
    A.pointHeight A.hFal A.hGR A.metricLog A.minimal_model A.faltings_wronskian A.GR_normalization

theorem jacobian_49_over_8 (K:Type*) [Field K] [NumberField K]
    {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {g i d N:ℕ} (D:CuspArakelovData318.Data K g i N)
    (F:FiniteData ι κ (2^128+i) d N) (A:ArakelovIdentifications K D F)
    (hg:2≤g) (hi:i≤g^3+1) (hgd:g≤d) (hN:1≤N)
    (R:ℝ) (hR:1≤R) (hindex:(d:ℝ)<2^14*C*R^((97:ℝ)/32))
    (hlevel:(N:ℝ)≤C*R^2) :
    A.hGR<2^65*C^2*R^((49:ℝ)/8) := by
  apply ActualLogWeight318.actual_jacobian_growth R d N A.hGR hR
    (by exact_mod_cast (show 1≤d by omega)) (by exact_mod_cast hN) hindex hlevel
  exact jacobian_quadratic K D F A hg hi hgd hN

/-- The adopted non-CM contact exponent from actual cusp/divisor data. The
image, isogeny and geometric contact inequalities are named producer inputs;
no contact or Jacobian bound is hidden among them. -/
theorem nonCM_contact_49_over_8 (K:Type*) [Field K] [NumberField K]
    {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {g i d N:ℕ} (D:CuspArakelovData318.Data K g i N)
    (F:FiniteData ι κ (2^128+i) d N) (A:ArakelovIdentifications K D F)
    (hg:2≤g) (hi:i≤g^3+1) (hgd:g≤d) (hN:1≤N)
    (R:ℝ) (hR:1≤R) (hindex:(d:ℝ)<2^14*C*R^((97:ℝ)/32))
    (hlevel:(N:ℝ)≤C*R^2)
    (degree hImage hSurface hContact:ℝ)
    (image_height:hImage≤A.hGR+3*(g:ℝ)/2)
    (degree_pos:0<degree) (degree_bound:degree≤2304*R)
    (isogeny_variation:hSurface≤hImage+8*(32*Real.log 14+Real.log degree+
      Real.log (max 1 (max (Real.log degree) hImage))))
    (contact_metric:hContact≤2*hSurface+120) :
    hContact<2^68*C^2*R^((49:ℝ)/8)+128 := by
  apply IsogenyHeightTransfer318.source_nonCM_height R d N g degree A.hGR hImage hSurface hContact
    hR (by exact_mod_cast (show 1≤d by omega)) (by exact_mod_cast hN)
    (by exact_mod_cast hgd) hindex hlevel
    (jacobian_quadratic K D F A hg hi hgd hN) image_height degree_pos degree_bound
    isogeny_variation contact_metric

end SourceNonCMHeight318
#print axioms SourceNonCMHeight318.jacobian_quadratic
#print axioms SourceNonCMHeight318.jacobian_49_over_8
#print axioms SourceNonCMHeight318.nonCM_contact_49_over_8
