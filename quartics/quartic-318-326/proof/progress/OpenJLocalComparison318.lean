module
public import LocalShortScaling318
public import OpenJScalingAmbiguity318
public import QuotientJ318
public section
noncomputable section
namespace OpenJLocalComparison318
open OpenJComplexEvaluation318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 0

@[expose] def j (z : ℂ) : ℂ := ActualQJ318.jInvariant (UpperHalfPlane.ofComplex z)
@[expose] def A (z : ℂ) : ℂ := -3*j z*(j z-1728)⁻¹
@[expose] def B (z : ℂ) : ℂ := -2*j z*(j z-1728)⁻¹
@[expose] def C (z : ℂ) : ℂ := (ModularWeierstrass318.curve (UpperHalfPlane.ofComplex z)).a₄
@[expose] def D (z : ℂ) : ℂ := (ModularWeierstrass318.curve (UpperHalfPlane.ofComplex z)).a₆

lemma j_analyticAt (tau : UpperHalfPlane) : AnalyticAt ℂ j (tau:ℂ) :=
  (UpperHalfPlane.contMDiffAt_iff.mp (QuotientJ318.j_holomorphic tau)).analyticAt

lemma coefficient_analyticAt (tau : UpperHalfPlane) (h : Admissible tau) :
    AnalyticAt ℂ A (tau:ℂ) ∧ AnalyticAt ℂ B (tau:ℂ) ∧
    AnalyticAt ℂ C (tau:ℂ) ∧ AnalyticAt ℂ D (tau:ℂ) := by
  have hj := j_analyticAt tau
  have hn : j (tau:ℂ)-1728≠0 := by simpa [j] using sub_ne_zero.mpr h.2
  have hi := (hj.sub analyticAt_const).inv hn
  have he4 : AnalyticAt ℂ (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex z)) (tau:ℂ) := by
    exact (UpperHalfPlane.mdifferentiable_iff.mp
      (ModularForm.E (k:=4) (by norm_num)).holo').analyticOnNhd
        UpperHalfPlane.isOpen_upperHalfPlaneSet tau tau.im_pos
  have he6 : AnalyticAt ℂ (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex z)) (tau:ℂ) := by
    exact (UpperHalfPlane.mdifferentiable_iff.mp
      (ModularForm.E (k:=6) (by norm_num)).holo').analyticOnNhd
        UpperHalfPlane.isOpen_upperHalfPlaneSet tau tau.im_pos
  exact ⟨(analyticAt_const.mul hj).mul hi,(analyticAt_const.mul hj).mul hi,
    he4.neg.div_const,he6.neg.div_const⟩

lemma admissible_eventually (tau : UpperHalfPlane) (h : Admissible tau) :
    ∀ᶠ z in 𝓝 (tau:ℂ), Admissible (UpperHalfPlane.ofComplex z) := by
  have hc := (j_analyticAt tau).continuousAt
  have h0 : j (tau:ℂ)≠0 := by simpa [j] using h.1
  have h1728 : j (tau:ℂ)≠1728 := by simpa [j] using h.2
  filter_upwards [hc.eventually_ne h0,hc.eventually_ne h1728] with z hz0 hz1728
  exact ⟨hz0,hz1728⟩

lemma fiber_coefficients (N : ℕ) [NeZero N] (z : ℂ)
    (h : Admissible (UpperHalfPlane.ofComplex z)) :
    (fiber N (UpperHalfPlane.ofComplex z) h).a₄=A z ∧
    (fiber N (UpperHalfPlane.ofComplex z) h).a₆=B z := by
  rw [fiber_eq]
  exact ⟨rfl,rfl⟩

/-- At every point of the actual open j-chart, the literal arithmetic family
and the genuine Eisenstein family admit an actual local holomorphic scaling.
The scaling at the basepoint is the previously selected one. -/
theorem exists_local_comparison (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u (tau:ℂ) ∧ u (tau:ℂ)=OpenJAnalyticPoints318.scaling N tau h ∧
      ∀ᶠ z in 𝓝 (tau:ℂ), ∃ hz : Admissible (UpperHalfPlane.ofComplex z),
        u z≠0 ∧
        (ModularWeierstrass318.curve (UpperHalfPlane.ofComplex z)).a₄=
          u z^4*(fiber N (UpperHalfPlane.ofComplex z) hz).a₄ ∧
        (ModularWeierstrass318.curve (UpperHalfPlane.ofComplex z)).a₆=
          u z^6*(fiber N (UpperHalfPlane.ofComplex z) hz).a₆ := by
  have hc := coefficient_analyticAt tau h
  have hcoeff : (fiber N tau h).a₄=A (tau:ℂ) ∧ (fiber N tau h).a₆=B (tau:ℂ) := by
    simpa using fiber_coefficients N (tau:ℂ) (by simpa using h)
  have hA : A (tau:ℂ)≠0 := hcoeff.1 ▸ OpenJScalingAmbiguity318.fiber_a4_ne_zero N tau h
  have hB : B (tau:ℂ)≠0 := hcoeff.2 ▸ OpenJScalingAmbiguity318.fiber_a6_ne_zero N tau h
  have hs := OpenJAnalyticPoints318.scaling_spec N tau h
  have hs4 : C (tau:ℂ)=(OpenJAnalyticPoints318.scaling N tau h:ℂ)^4*A (tau:ℂ) := by
    simpa [C,hcoeff.1] using hs.1
  have hs6 : D (tau:ℂ)=(OpenJAnalyticPoints318.scaling N tau h:ℂ)^6*B (tau:ℂ) := by
    simpa [D,hcoeff.2] using hs.2
  have hex : ∀ᶠ z in 𝓝 (tau:ℂ), ∃ u : ℂˣ, C z=(u:ℂ)^4*A z ∧ D z=(u:ℂ)^6*B z := by
    filter_upwards [admissible_eventually tau h] with z hz
    obtain ⟨u,hu4,hu6⟩ := OpenJAnalyticPoints318.exists_scaling N (UpperHalfPlane.ofComplex z) hz
    exact ⟨u,by simpa [C,(fiber_coefficients N z hz).1] using hu4,
      by simpa [D,(fiber_coefficients N z hz).2] using hu6⟩
  obtain ⟨u,hu,hu0,huCoeff⟩ := LocalShortScaling318.exists_local_scaling A B C D (tau:ℂ)
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hA hB (OpenJAnalyticPoints318.scaling N tau h) hs4 hs6 hex
  refine ⟨u,hu,hu0,?_⟩
  filter_upwards [admissible_eventually tau h,huCoeff] with z hz huc
  exact ⟨hz,huc.1,by simpa [C,(fiber_coefficients N z hz).1] using huc.2.1,
    by simpa [D,(fiber_coefficients N z hz).2] using huc.2.2⟩

end OpenJLocalComparison318
