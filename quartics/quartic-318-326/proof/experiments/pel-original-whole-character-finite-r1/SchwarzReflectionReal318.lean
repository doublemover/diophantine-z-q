module
public import HolomorphicGluingAcrossReal318
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Topology.Piecewise
public section
noncomputable section
namespace SchwarzReflectionReal318
open Complex Set Filter Metric
open scoped Topology ComplexConjugate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000

@[expose] def upperClosed : Set ℂ := {z | 0≤z.im}
@[expose] def lowerClosed : Set ℂ := {z | z.im≤0}
@[expose] def extension (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0≤z.im then f z else conj (f (conj z))

theorem upperClosed_closed : IsClosed upperClosed := isClosed_le continuous_const Complex.continuous_im
theorem lowerClosed_closed : IsClosed lowerClosed := isClosed_le Complex.continuous_im continuous_const

theorem frontier_upper_im_zero (z : ℂ) (hz : z∈frontier upperClosed) : z.im=0 := by
  have hge : 0≤z.im := by
    have hh := hz.1
    rw [upperClosed_closed.closure_eq] at hh
    exact hh
  have hn : ¬0<z.im := by
    intro hp
    apply hz.2
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hp)
        (fun w hw => hw.le))
  exact le_antisymm (le_of_not_gt hn) hge

theorem closure_upper_compl_subset : closure upperClosedᶜ⊆lowerClosed := by
  apply closure_minimal _ lowerClosed_closed
  intro z hz
  change ¬0≤z.im at hz
  change z.im≤0
  exact (lt_of_not_ge hz).le

theorem conjugate_of_im_zero (z : ℂ) (hz : z.im=0) : conj z=z := by
  apply Complex.ext <;> simp [hz]

/-- Continuity across the seam is constructed from continuity on the
closed upper side and real values on the seam. It is not an extra input
about the reflected extension. -/
theorem extension_continuousOn (f : ℂ → ℂ) (U : Set ℂ)
    (hU : ∀z∈U,conj z∈U)
    (hf : ContinuousOn f (U∩upperClosed))
    (hr : ∀z∈U,z.im=0 → (f z).im=0) : ContinuousOn (extension f) U := by
  have hconj : Continuous (conj : ℂ → ℂ) := continuous_star
  have hg : ContinuousOn (fun z => conj (f (conj z))) (U∩lowerClosed) :=
    hconj.continuousOn.comp
      (hf.comp hconj.continuousOn (by
        intro z hz
        refine ⟨hU z hz.1,?_⟩
        change 0≤(conj z).im
        simpa only [Complex.conj_im] using neg_nonneg.mpr hz.2)) (by
          intro z hz
          exact Set.mem_univ _)
  unfold extension
  apply ContinuousOn.if
  · intro z hz
    have hz0 := frontier_upper_im_zero z hz.2
    rw [conjugate_of_im_zero z hz0,conjugate_of_im_zero (f z) (hr z hz.1 hz0)]
  · change ContinuousOn f (U∩closure upperClosed)
    rw [upperClosed_closed.closure_eq]
    exact hf
  · apply hg.mono
    intro z hz
    exact ⟨hz.1,closure_upper_compl_subset hz.2⟩

/-- Schwarz reflection across a real interval on an arbitrary conjugation-
invariant open domain. Holomorphy on the lower side is obtained by genuine
conjugate-conjugate differentiation; Morera proves holomorphy AT the seam. -/
theorem extension_differentiableOn (f : ℂ → ℂ) (U : Set ℂ)
    (hopen : IsOpen U) (hU : ∀z∈U,conj z∈U)
    (hf : ContinuousOn f (U∩upperClosed))
    (hd : ∀z∈U,0<z.im → DifferentiableAt ℂ f z)
    (hr : ∀z∈U,z.im=0 → (f z).im=0) : DifferentiableOn ℂ (extension f) U := by
  apply HolomorphicGluingAcrossReal318.differentiableOn_of_continuousOn_off_real
    (extension f) U hopen (extension_continuousOn f U hU hf hr)
  intro z hz hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hzc : 0<(conj z).im := by simpa only [Complex.conj_im] using neg_pos.mpr hneg
    have hh : DifferentiableAt ℂ (conj ∘ f ∘ conj) z :=
      differentiableAt_conj_conj_iff.mpr (hd (conj z) (hU z hz) hzc)
    apply (hh.hasDerivAt.congr_of_eventuallyEq ?_).differentiableAt
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg] with w hw
    simp only [extension,if_neg (not_le.mpr hw),Function.comp_apply]
  · apply ((hd z hz hpos).hasDerivAt.congr_of_eventuallyEq ?_).differentiableAt
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos] with w hw
    simp only [extension,if_pos hw.le]

theorem extension_agrees (f : ℂ → ℂ) (z : ℂ) (hz : 0≤z.im) : extension f z=f z := by
  simp only [extension,if_pos hz]

/-- The constructed holomorphic extension retains the original reflected
formula on the entire lower open side, not just a boundary germ. -/
theorem extension_lower (f : ℂ → ℂ) (z : ℂ) (hz : z.im<0) :
    extension f z=conj (f (conj z)) := by
  simp only [extension,if_neg (not_le.mpr hz)]
end SchwarzReflectionReal318
