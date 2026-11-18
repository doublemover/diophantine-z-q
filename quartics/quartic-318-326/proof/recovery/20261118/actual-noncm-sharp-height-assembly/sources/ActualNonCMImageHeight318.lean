module
public import SameSurfaceFiveContactBridge318
public section
noncomputable section
namespace ActualNonCMImageHeight318
open NumberField ContactHeight318 FiveContactProducer318 RefinedContactRealization318
open ActualPELMetricSections318 SourceJacobianBound318
set_option maxHeartbeats 1000000

/-- From stable Rémond on the actual inclusion C_A⊂J_H and Bost on J_H/C_A.
The dimension shift b per dimension is common, with b≥0. Actual source image
dimension is 2; hence in fact the count is g−2, including quotient dimension 0. -/
theorem image_from_stable {g j c t b : ℝ} (hg : 2≤g) (hb : 0≤b)
    (remond : c+t≤j) (bost : -(3/2)*(g-2)≤t) :
    c+2*b≤(j+g*b)+3*g/2 := by
  have hm := mul_nonneg (sub_nonneg.mpr hg) hb
  nlinarith

/-- Dimension-two GR in its original normalization on the image as source,
not on the genus-g Jacobian. Shift A and C_A equally before the final step. -/
theorem variation_from_degree {d deg c a b : ℝ}
    (hd : 0<d) (hdg : 0<deg) (hb : 0≤b)
    (hGR : deg≤(CMIsogeny318.Xi d c)^2)
    (variation : a≤c+1/2*Real.log deg) :
    a+2*b≤c+2*b+8*(32*Real.log 14+Real.log d+
      Real.log (max 1 (max (Real.log d) (c+2*b)))) := by
  have hx := CMIsogeny318.half_log_degree d c deg hd hdg hGR
  have hm := IsogenyHeightTransfer318.half_log_expression_mono d c (c+2*b) (by linarith)
  linarith

/-- Build the old NonCMInputs from its true cusp/finite/Arakelov data,
the original stable heights of the actual Jacobian image, quotient and surface,
the actual dimension-two relative isogeny degree, and the *original* named
inequalities. Neither an image bound nor the expanded variation nor a final
surface/contact estimate is a supplied field. -/
@[expose] def inputs {K : Type*} [Field K] [NumberField K] {u v : ℤ}
    (g i d N nex nout : ℕ) (D : CuspArakelovData318.Data K g i N)
    (F : FiniteData (Fin nex) (Fin nout) (2^128+i) d N)
    (Ar : SourceNonCMHeight318.ArakelovIdentifications K D F)
    (hg : 2≤g) (hi : i≤g^3+1) (hgd : g≤d) (hN : 1≤N)
    (hindex : (d:ℝ)<2^14*ActualLogWeight318.C*(support u v)^((97:ℝ)/32))
    (hlevel : (N:ℝ)≤ActualLogWeight318.C*(support u v)^2)
    (df deg c t a : ℝ)
    (hdf : 0<df) (hdfb : df≤2304*support u v) (hdg : 0<deg)
    (hrem : c+t≤Ar.hFal) (hbost : -(3/2)*((g:ℝ)-2)≤t)
    (hGR : deg≤(CMIsogeny318.Xi df c)^2) (hvar : a≤c+1/2*Real.log deg) :
    NonCMInputs K u v := by
  let b:=Real.log (Real.sqrt Real.pi)
  have hb : 0≤b := Real.log_nonneg (by
    have hh := Real.sqrt_le_sqrt (show (1:ℝ)≤Real.pi by linarith [Real.pi_gt_three])
    simpa using hh)
  refine {genus:=g,candidate:=i,coverDegree:=d,level:=N,exceptionalCount:=nex,outsideCount:=nout,
    cusp:=D,finiteData:=F,arakelov:=Ar,genus_lower:=hg,candidate_bound:=hi,genus_degree:=hgd,
    level_pos:=hN,index_bound:=hindex,level_bound:=hlevel,isogenyFieldDegree:=df,
    imageHeight:=c+2*b,surfaceHeight:=a+2*b,field_pos:=hdf,field_bound:=hdfb,
    image_bound:=?_,isogeny_variation:=variation_from_degree hdf hdg hb hGR hvar}
  rw [Ar.GR_normalization]
  exact image_from_stable (by exact_mod_cast hg) hb hrem hbost

/-- Direct per-point contact target, without assuming an old NonCMInputs
record, its two final arithmetic fields, or its contact bound. The actual
metric datum is indexed by original A-height plus log π; all independent
geometric and arithmetic inputs are displayed. -/
theorem target {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] {u v : ℤ}
    (g i d N nex nout : ℕ) (D : CuspArakelovData318.Data K g i N)
    (F : FiniteData (Fin nex) (Fin nout) (2^128+i) d N)
    (Ar : SourceNonCMHeight318.ArakelovIdentifications K D F)
    (hg : 2≤g) (hi : i≤g^3+1) (hgd : g≤d) (hN : 1≤N)
    (hindex : (d:ℝ)<2^14*ActualLogWeight318.C*(support u v)^((97:ℝ)/32))
    (hlevel : (N:ℝ)≤ActualLogWeight318.C*(support u v)^2)
    (df deg c t a : ℝ)
    (hdf : 0<df) (hdfb : df≤2304*support u v) (hdg : 0<deg)
    (hrem : c+t≤Ar.hFal) (hbost : -(3/2)*((g:ℝ)-2)≤t)
    (hGR : deg≤(CMIsogeny318.Xi df c)^2) (hvar : a≤c+1/2*Real.log deg)
    (T : Datum L u v (a+Real.log Real.pi)) :
    pointHeight u v<2^68*((210:ℝ)^300)^2*(support u v)^((49:ℝ)/8)+128 := by
  let M := @inputs K _ _ u v g i d N nex nout D F Ar hg hi hgd hN hindex hlevel
    df deg c t a hdf hdfb hdg hrem hbost hGR hvar
  have he : M.surfaceHeight=a+2*Real.log (Real.sqrt Real.pi) := rfl
  have hcontact := (metricSections T).original_bound
  have hc : pointHeight u v≤2*M.surfaceHeight+120 := by
    rw [he,Real.log_sqrt Real.pi_pos.le]
    linarith [Real.log_nonneg (show (1:ℝ)≤Real.pi by linarith [Real.pi_gt_three])]
  exact (SameSurfaceFiveContactBridge318.noncmFromBound M hc).bound

end ActualNonCMImageHeight318
