module
public import PELOriginalCoarseDeterminantFrames318
public section
noncomputable section
namespace PELOriginalCoarseDeterminantMetric318
open QuaternionicJointPeriodTopology318 PELUnlevelledComplexBase318
open PELOriginalDeterminantCover318 PELOriginalCoarseDeterminantBundle318
open PELOriginalCoarseDeterminantFrames318 PELOriginalDeterminantMetricTransition318

@[expose] def metricFrame (q : UnlevelledBase) : Fiber q ≃ₗ[ℂ] ℂ :=
  LinearEquiv.smulOfUnit (Units.mk0 (scale (chart (core.indexAt q) q:ℂ):ℂ)
    (Complex.ofReal_ne_zero.mpr (scale_positive _ (chart (core.indexAt q) q).property).ne'))
@[expose] def normedGroup (q : UnlevelledBase) : NormedAddCommGroup (Fiber q) :=
  NormedAddCommGroup.induced _ ℂ (metricFrame q).toAddMonoidHom (metricFrame q).injective
@[expose] def normedSpace (q : UnlevelledBase) :
    letI := normedGroup q
    NormedSpace ℂ (Fiber q) := by
  letI := normedGroup q
  refine { norm_smul_le := ?_ }
  intro a x
  change ‖metricFrame q (a • x)‖≤‖a‖*‖metricFrame q x‖
  rw [map_smul,norm_smul]
@[expose] def normValue (q : UnlevelledBase) (x : Fiber q) : ℝ := ‖metricFrame q x‖
lemma chosen_formula (q : UnlevelledBase) (x : Fiber q) :
    normValue q x=scale (chart (core.indexAt q) q:ℂ)*‖x‖ := by
  change ‖(scale (chart (core.indexAt q) q:ℂ):ℂ)*x‖=_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (scale_positive _ (chart (core.indexAt q) q).property)]

/-- EVERY actual covering chart computes the same whole-fiber norm.
This removes the auxiliary choice of core index from the metric. -/
theorem local_formula (a : HalfPlane) (q : UnlevelledBase) (ha : q∈baseSet a)
    (x : Fiber q) : normValue q x=scale (chart a q:ℂ)*‖localCoordinate a q x‖ := by
  have h := local_norm_change (core.indexAt q) a q (core.mem_baseSet_at q) ha x
  rw [localCoordinate_apply,transition_self,one_mul] at h
  exact (chosen_formula q x).trans h.symm

/-- The local frame is an isometry to the GENUINE exterior kernel
metric, on every vector and every chart, with its original normalization. -/
theorem actual_exterior_norm (a : HalfPlane) (q : UnlevelledBase) (ha : q∈baseSet a)
    (x : Fiber q) :
    PELOriginalNormedKernelDeterminant318.normValue (chart a q:ℂ) (chart a q).property
      (exteriorFrame a q x)=normValue q x := by
  rw [PELOriginalNormedKernelDeterminant318.norm_formula,exteriorFrame_coordinate,
    local_formula a q ha]
lemma scale_continuous : Continuous (fun τ : HalfPlane=>scale (τ:ℂ)) := by
  have he : (fun τ : HalfPlane=>scale (τ:ℂ))=(fun τ : HalfPlane=>
      Real.sqrt (42*(τ:ℂ).im^2/Complex.normSq (τ:ℂ))) := by
    funext τ
    unfold scale
    rw [PELOriginalPeriodMetricDeterminant318.imaginary_determinant τ τ.property]
  rw [he]
  exact Real.continuous_sqrt.comp ((continuous_const.mul
    ((Complex.continuous_im.comp continuous_subtype_val).pow 2)).div
      (Complex.continuous_normSq.comp continuous_subtype_val)
      (fun τ=>(Complex.normSq_pos.mpr
        (PELOriginalSiegelNormalization318.parameter_ne τ τ.property)).ne'))

/-- The descended norm is continuous on the ACTUAL total space, verified
in genuine bundle trivializations rather than by continuity of the
arbitrarily selected global fiber gauge. -/
theorem total_norm_continuous : Continuous (fun p : Total=>normValue p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let a : HalfPlane := core.indexAt p.1
  have ha : p.1∈baseSet a := core.mem_baseSet_at p.1
  have hp : ContinuousAt (fun r : Total=>r.1) p := projection_continuous.continuousAt
  have ht : ContinuousAt (core.localTriv a) p := (core.localTriv a).continuousAt ha
  have hs := scale_continuous.continuousAt.comp (((chart a).continuousAt ha).comp hp)
  have h := hs.mul ht.snd.norm
  apply h.congr_of_eventuallyEq
  have hn := hp.eventually ((chart a).open_source.mem_nhds ha)
  filter_upwards [hn] with r hr
  exact (local_formula a r.1 hr r.2).symm
end PELOriginalCoarseDeterminantMetric318
