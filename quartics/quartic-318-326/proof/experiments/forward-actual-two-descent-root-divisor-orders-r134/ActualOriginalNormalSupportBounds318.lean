module
public import ActualOriginalIntervalSubstitution318
public section
noncomputable section
namespace ActualOriginalNormalSupportBounds318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318 ActualOriginalJointLevelDensity318
open ActualOriginalNormalLevelChart318 ActualOriginalNormalJacobian318
set_option maxHeartbeats 16000000

/-- ONE pair of positive finite normal-coordinate endpoints works for the
whole original compact support, hence for every later parameter slice. -/
theorem actual_uniform_normal_bounds (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hWc : HasCompactSupport W)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0) :
    ∃A B : ℝ,0<A ∧ A<B ∧ ∀x∈tsupport W,A<x.1.1 ∧ x.1.1<B := by
  have hbd : BddAbove ((fun x : Coordinates ℝ => x.1.1) '' tsupport W) :=
    hWc.isCompact.bddAbove_image (show ContinuousOn (fun x : Coordinates ℝ => x.1.1) (tsupport W) by fun_prop)
  obtain ⟨B,hB⟩ := hbd
  refine ⟨η/4,max (η/4) B+1,by positivity,?_,?_⟩
  · have hh := le_max_left (η/4) B
    linarith
  · intro x hx
    have h := hb x hx
    change η<2*x.1.1 at h
    have h' := hB ⟨x,hx,rfl⟩
    have hmax := le_max_right (η/4) B
    constructor <;> linarith

lemma actual_normal_endpoint_order (κ A B : ℝ) (hA : 0<A) (hAB : A<B) (v : Parameters) :
    equation κ (assemble A v)<equation κ (assemble B v) := by
  rw [original_normal_polynomial,original_normal_polynomial]
  nlinarith [mul_pos (sub_pos.mpr hAB) (by linarith : 0<B+A)]

lemma source_outside_normal_bounds (W : Coordinates ℝ→ℝ) (A B : ℝ)
    (hb : ∀x∈tsupport W,A<x.1.1 ∧ x.1.1<B) (v : Parameters)
    (a : ℝ) (ha : a∉Set.Icc A B) : W (assemble a v)=0 := by
  by_contra hh
  have h := hb (assemble a v) (subset_closure hh)
  exact ha ⟨h.1.le,h.2.le⟩

/-- The same actual bounds force the exact normal-level density to vanish
outside the transformed interval; no independent cutoff is chosen per v. -/
lemma density_outside_normal_bounds (κ : ℝ) (W : Coordinates ℝ→ℝ) (A B : ℝ)
    (hA : 0<A) (hAB : A<B)
    (hb : ∀x∈tsupport W,A<x.1.1 ∧ x.1.1<B) (v : Parameters) (s : ℝ)
    (hs : s∉Set.Icc (equation κ (assemble A v)) (equation κ (assemble B v))) :
    levelDensity κ W (s,v)=0 := by
  by_contra hh
  have hw : W (levelGraph κ (s,v))≠0 := by
    intro hz
    exact hh (by simp only [levelDensity,hz,zero_div])
  have hb' := hb (levelGraph κ (s,v)) (subset_closure hw)
  change A<Real.sqrt (radicand κ v+s) ∧ Real.sqrt (radicand κ v+s)<B at hb'
  have hpos : 0<Real.sqrt (radicand κ v+s) := lt_trans hA hb'.1
  have hrad : 0<radicand κ v+s := Real.sqrt_pos.mp hpos
  have hsq := Real.sq_sqrt hrad.le
  apply hs
  rw [original_normal_polynomial,original_normal_polynomial]
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hb'.1) (by linarith : 0<Real.sqrt (radicand κ v+s)+A)]
  · nlinarith [mul_pos (sub_pos.mpr hb'.2) (by linarith : 0<B+Real.sqrt (radicand κ v+s))]

end ActualOriginalNormalSupportBounds318
