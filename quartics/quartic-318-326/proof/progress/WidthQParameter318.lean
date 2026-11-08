module
public import RotatedCuspOrbit318
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318
open PeterssonQuotient318
namespace WidthQParameter318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def high (A:ℝ) : Set UpperHalfPlane := {tau | A<tau.im}
@[expose] def radius (w A:ℝ) : ℝ := Real.exp (-2*Real.pi*A/w)
@[expose] def punctured (w A:ℝ) : Set ℂ := {q | q≠0 ∧ ‖q‖<radius w A}
theorem high_open (A:ℝ) : IsOpen (high A) := isOpen_lt continuous_const continuous_im

theorem radius_positive (w A:ℝ) : 0<radius w A := Real.exp_pos _

theorem radius_lt_one (w A:ℝ) (hw:0<w) (hA:0<A) : radius w A<1 := by
  rw [radius,Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) hw

theorem qParam_maps (w A:ℝ) (hw:0<w) : Set.MapsTo (fun tau:UpperHalfPlane=>Periodic.qParam w tau)
    (high A) (punctured w A) := by
  intro tau htau
  refine ⟨Periodic.qParam_ne_zero _,?_⟩
  simpa only [radius] using
    (Periodic.norm_qParam_lt_iff hw A tau).mpr htau

/-- Genuine exponential coordinate on the high half-plane. -/
@[expose] def qMap (w A:ℝ) (hw:0<w) : high A → punctured w A := (qParam_maps w A hw).restrict

theorem qParam_isOpenMap (w:ℝ) (hw:0<w) : IsOpenMap (fun tau:UpperHalfPlane=>Periodic.qParam w tau) := by
  have he : Periodic.qParam w = fun z:ℂ => Complex.exp ((2*Real.pi*Complex.I/w)*z) := by
    funext z
    simp only [Periodic.qParam]
    congr 1
    ring
  have h : IsOpenMap (Periodic.qParam w) := by
    rw [he]
    exact Complex.isOpenMap_exp.comp
      (Homeomorph.mulLeft₀ (2*Real.pi*Complex.I/w:ℂ)
        (div_ne_zero Complex.two_pi_I_ne_zero (Complex.ofReal_ne_zero.mpr hw.ne'))).isOpenMap
  exact h.comp UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

theorem qMap_continuous (w A:ℝ) (hw:0<w) : Continuous (qMap w A hw) :=
  ((Periodic.continuous_qParam (h:=w)).comp (continuous_coe.comp continuous_subtype_val)).subtype_mk _

theorem qMap_isOpenMap (w A:ℝ) (hw:0<w) : IsOpenMap (qMap w A hw) :=
  ((qParam_isOpenMap w hw).domRestrict (high_open A)).codRestrict _

theorem qMap_surjective (w A:ℝ) (hw:0<w) (hA:0<A) : Function.Surjective (qMap w A hw) := by
  intro q
  have hinv : A<(Periodic.invQParam w q).im := by
    apply (Periodic.norm_qParam_lt_iff hw A _).mp
    rw [Periodic.qParam_right_inv hw.ne' q.property.1]
    simpa only [radius] using q.property.2
  let tau:UpperHalfPlane := ⟨Periodic.invQParam w q,lt_trans hA hinv⟩
  refine ⟨⟨tau,hinv⟩,?_⟩
  apply Subtype.ext
  exact Periodic.qParam_right_inv hw.ne' q.property.1

end WidthQParameter318
