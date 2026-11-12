module
public import PELOriginalRealBranchIntervals318
public import ConnectedSquareRootComparison318
public section
noncomputable section
namespace LegendreRealStripSheets318
open Set
open PELOriginalRealStripCover318 PELOriginalFourBranchCoordinate318
open PELOriginalRealBranchParameters318 ComplexVerticalStrip318
open LegendreHalfPlaneAnalyticSheets318 NormalizedLegendreFieldPoints318
variable {i:Fin 4} (J:Interval i)
set_option maxHeartbeats 1000000

lemma polynomial_nonzero_strip (z:ℂ) (hz:z∈J.Domain) :
    polynomial (branchParameter i) z≠0 := by
  unfold polynomial
  apply mul_ne_zero
  · apply mul_ne_zero
    · intro h
      subst z
      exact J.zero_not hz
    · intro h
      have he:=sub_eq_zero.mp h
      subst z
      exact J.one_not hz
  · intro h
    have he:=sub_eq_zero.mp h
    subst z
    exact J.parameter_not hz

/-- Actual globally analytic root on the ENTIRE real strip, including
all real seam points, of the same original normalized Legendre polynomial. -/
theorem exists_strip_root : ∃s:ℂ→ℂ,AnalyticOnNhd ℂ s J.Domain ∧
    ∀z,s z^2=polynomial (branchParameter i) z := by
  apply AnalyticNonzeroSquareRoot318.exists_analytic_root
    (strip_open J.isOpen) (strip_simplyConnected J.convex ⟨J.point,J.point_mem⟩)
  · exact (polynomial_analytic _).mono (subset_univ _)
  · exact polynomial_nonzero_strip J
@[expose] def stripRoot : ℂ→ℂ := (exists_strip_root J).choose
lemma stripRoot_analytic : AnalyticOnNhd ℂ (stripRoot J) J.Domain :=
  (exists_strip_root J).choose_spec.1
lemma stripRoot_square (z:ℂ) : stripRoot J z^2=polynomial (branchParameter i) z :=
  (exists_strip_root J).choose_spec.2 z
lemma stripRoot_nonzero (z:ℂ) (hz:z∈J.Domain) : stripRoot J z≠0 := by
  intro h
  have hh:=stripRoot_square J z
  rw [h,zero_pow (by decide : 2≠0)] at hh
  exact polynomial_nonzero_strip J z hz hh.symm

/-- Each OLD fixed halfplane root differs by one constant sign from this
whole-strip root on the ENTIRE half-strip, not at just one chosen point. -/
theorem exists_half_sign (upper:Bool) : ∃s:ℂ,s^2=1 ∧
    ∀z∈J.HalfDomain upper,
      root (branchParameter i) (branchParameter_im_zero i) upper z=s*stripRoot J z := by
  apply ConnectedSquareRootComparison318.exists_sign
    (halfStrip_convex J.convex upper).isPreconnected
    (halfStrip_nonempty ⟨J.point,J.point_mem⟩ upper)
  · exact (root_analytic _ _ upper).continuousOn.mono (fun _ h=>h.2)
  · exact (stripRoot_analytic J).continuousOn.mono (fun _ h=>h.1)
  · intro z _
    rw [root_square,stripRoot_square]
  · exact fun z hz=>stripRoot_nonzero J z hz.1
@[expose] def halfSign (upper:Bool) : ℂ := (exists_half_sign J upper).choose
lemma halfSign_square (upper:Bool) : halfSign J upper^2=1 :=
  (exists_half_sign J upper).choose_spec.1
lemma halfSign_formula (upper:Bool) (z:ℂ) (hz:z∈J.HalfDomain upper) :
    root (branchParameter i) (branchParameter_im_zero i) upper z=
      halfSign J upper*stripRoot J z := (exists_half_sign J upper).choose_spec.2 z hz

/-- One target sign transition across this whole real component. Its
square is one, and it is constructed from the already fixed roots. -/
@[expose] def transitionSign : ℂ := halfSign J true*halfSign J false
lemma transitionSign_square : transitionSign J^2=1 := by
  rw [transitionSign,mul_pow,halfSign_square,halfSign_square,one_mul]

/-- A single holomorphic function equals the OLD positive upper sheet
and exactly its matched lower sheet throughout the respective halfstrips.
This supplies actual target seam continuation, not a branch-count slogan. -/
theorem analytic_continuation : ∃F:ℂ→ℂ,
    AnalyticOnNhd ℂ F J.Domain ∧ (∀z,F z^2=polynomial (branchParameter i) z) ∧
    (∀z∈J.HalfDomain true,F z=root (branchParameter i) (branchParameter_im_zero i) true z) ∧
    (∀z∈J.HalfDomain false,F z=transitionSign J*
      root (branchParameter i) (branchParameter_im_zero i) false z) := by
  refine ⟨fun z=>halfSign J true*stripRoot J z,?_,?_,?_,?_⟩
  · intro z hz
    exact analyticAt_const.mul (stripRoot_analytic J z hz)
  · intro z
    rw [mul_pow,halfSign_square,one_mul,stripRoot_square]
  · intro z hz
    exact (halfSign_formula J true z hz).symm
  · intro z hz
    rw [halfSign_formula J false z hz,transitionSign]
    have hs:=halfSign_square J false
    linear_combination -(halfSign J true*stripRoot J z)*hs

/-- Every produced strip root is a point of the same original completed
Legendre target, with the exact full Scheme projection to its original t. -/
theorem strip_scheme_projection (z:ℂ) :
    NormalizedLegendreFiniteProjection318.project (branchParameter i)
      (schemeEquiv (branchParameter i) (some ⟨(z,stripRoot J z),stripRoot_square J z⟩))=
        ProjectiveLineComplexSchemePoints318.chartPoint 1 z :=
  NormalizedLegendreFiniteProjection318.finite_projection _ _
end LegendreRealStripSheets318
