module
public import CuspOrbit318
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318
open PeterssonQuotient318
namespace HighQParameter318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def high (A:ℝ) : Set UpperHalfPlane := {tau | A<tau.im}
@[expose] def radius (A:ℝ) : ℝ := Real.exp (-2*Real.pi*A)
@[expose] def punctured (A:ℝ) : Set ℂ := {q | q≠0 ∧ ‖q‖<radius A}
@[expose] def neighborhood (N:ℕ) (A:ℝ) : Set (Base (image N)) := quotientMap N '' high A

theorem high_open (A:ℝ) : IsOpen (high A) := isOpen_lt continuous_const continuous_im

theorem quotient_open (N:ℕ) : IsOpenMap (quotientMap N) :=
  MulAction.isOpenQuotientMap_quotientMk.isOpenMap

theorem neighborhood_open (N:ℕ) (A:ℝ) : IsOpen (neighborhood N A) :=
  quotient_open N _ (high_open A)

theorem radius_positive (A:ℝ) : 0<radius A := Real.exp_pos _

theorem radius_lt_one (A:ℝ) (hA:0<A) : radius A<1 := by
  rw [radius,Real.exp_lt_one_iff]
  have hp:=Real.pi_pos
  nlinarith

theorem qParam_maps (A:ℝ) : Set.MapsTo (fun tau:UpperHalfPlane=>Periodic.qParam 1 tau)
    (high A) (punctured A) := by
  intro tau htau
  refine ⟨Periodic.qParam_ne_zero _,?_⟩
  simpa only [radius,div_one] using
    (Periodic.norm_qParam_lt_iff (by norm_num : (0:ℝ)<1) A tau).mpr htau

/-- Genuine exponential coordinate on the high half-plane. -/
@[expose] def qMap (A:ℝ) : high A → punctured A := (qParam_maps A).restrict

/-- Genuine projection to the actual quotient neighborhood. -/
@[expose] def projection (N:ℕ) (A:ℝ) : high A → neighborhood N A :=
  fun tau => ⟨quotientMap N tau,⟨tau,tau.property,rfl⟩⟩

theorem projection_surjective (N:ℕ) (A:ℝ) : Function.Surjective (projection N A) := by
  rintro ⟨b,tau,htau,rfl⟩
  exact ⟨⟨tau,htau⟩,rfl⟩

theorem projection_continuous (N:ℕ) (A:ℝ) : Continuous (projection N A) :=
  (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _

theorem projection_isOpenMap (N:ℕ) (A:ℝ) : IsOpenMap (projection N A) :=
  ((quotient_open N).domRestrict (high_open A)).codRestrict _

theorem projection_quotient (N:ℕ) (A:ℝ) : Topology.IsQuotientMap (projection N A) :=
  (projection_isOpenMap N A).isQuotientMap (projection_continuous N A) (projection_surjective N A)

theorem qParam_isOpenMap : IsOpenMap (fun tau:UpperHalfPlane=>Periodic.qParam 1 tau) := by
  have he : Periodic.qParam 1 = fun z:ℂ => Complex.exp ((2*Real.pi*Complex.I)*z) := by
    funext z
    simp [Periodic.qParam]
  have h : IsOpenMap (Periodic.qParam 1) := by
    rw [he]
    exact Complex.isOpenMap_exp.comp
      (Homeomorph.mulLeft₀ (2*Real.pi*Complex.I:ℂ) Complex.two_pi_I_ne_zero).isOpenMap
  exact h.comp UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

theorem qMap_continuous (A:ℝ) : Continuous (qMap A) :=
  ((Periodic.continuous_qParam (h:=1)).comp (continuous_coe.comp continuous_subtype_val)).subtype_mk _

theorem qMap_isOpenMap (A:ℝ) : IsOpenMap (qMap A) :=
  (qParam_isOpenMap.domRestrict (high_open A)).codRestrict _

theorem qMap_surjective (A:ℝ) (hA:0<A) : Function.Surjective (qMap A) := by
  intro q
  have hinv : A<(Periodic.invQParam 1 q).im := by
    apply (Periodic.norm_qParam_lt_iff (by norm_num : (0:ℝ)<1) A _).mp
    rw [Periodic.qParam_right_inv (by norm_num : (1:ℝ)≠0) q.property.1]
    simpa only [radius,div_one] using q.property.2
  let tau:UpperHalfPlane := ⟨Periodic.invQParam 1 q,lt_trans hA hinv⟩
  refine ⟨⟨tau,hinv⟩,?_⟩
  apply Subtype.ext
  exact Periodic.qParam_right_inv (by norm_num : (1:ℝ)≠0) q.property.1

end HighQParameter318
