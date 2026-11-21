module

public import SelectedActualOrdinaryAbelPeriodMap318
public import Mathlib.Topology.LocallyConstant.Basic

public section

noncomputable section

open UpperHalfPlane Metric Set Filter
open scoped Topology
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedWeightTwoPetersson318 SelectedActualOrdinaryAbelPeriodMap318

namespace SelectedActualAbelPeriodAgreement318

variable {M g : ℕ} {J : Type*} [AddCommGroup J]

/-- Only genuine local lifts of the fixed map and their differential
are required. In the geometric application q is the actual exponential,
a is the restriction of the same algebraic Abel map via the established
compact comparison, and the derivative equality is its same invariant
differential comparison, not a period-zero condition. -/
def LocalOriginalLifts (f : Fin g → Form M) (q : (Fin g → ℂ) →+ J)
    (a : Base (image M) → J) : Prop :=
  ∀ τ : UpperHalfPlane, ∃ r : ℝ, 0 < r ∧ ball (τ : ℂ) r ⊆ upperHalfPlaneSet ∧
    ∃ ψ : Fin g → ℂ → ℂ,
      (∀ i z, z ∈ ball (τ : ℂ) r → HasDerivAt (ψ i) (f i (UpperHalfPlane.ofComplex z)) z) ∧
      (∀ z ∈ ball (τ : ℂ) r, q (fun i => ψ i z) = a (quotientMap M (UpperHalfPlane.ofComplex z)))

private theorem primitive_I_vector (f : Fin g → Form M) :
    primitiveVector f UpperHalfPlane.I = 0 := by
  funext i
  exact primitive_I (f i)

/-- Local equality of the original differential already pins down
the global period formula, with the literal basepoint translation.
No global lift to C^g and no period-zero input are assumed. -/
theorem original_value_from_local_lifts
    (f : Fin g → Form M) (q : (Fin g → ℂ) →+ J) (a : Base (image M) → J)
    (hLocal : LocalOriginalLifts f q a) (τ : UpperHalfPlane) :
    a (quotientMap M τ) = q (primitiveVector f τ) + a (quotientMap M UpperHalfPlane.I) := by
  let d (x : UpperHalfPlane) : J := a (quotientMap M x) - q (primitiveVector f x)
  have hl : IsLocallyConstant d := by
    apply (IsLocallyConstant.iff_eventually_eq d).mpr
    intro t
    unfold LocalOriginalLifts at hLocal
    obtain ⟨r,hr,hu,ψ,hψ,hval⟩ := hLocal t
    let B : Set ℂ := ball (t : ℂ) r
    let c (i : Fin g) : ℂ := ψ i (t : ℂ) - primitive (f i) (t : ℂ)
    have ht : (t : ℂ) ∈ B := mem_ball_self hr
    have hP (i : Fin g) (z : ℂ) (hz : z ∈ B) :
        HasDerivAt (fun w => primitive (f i) w + c i) (f i (UpperHalfPlane.ofComplex z)) z := by
      let v : UpperHalfPlane := ⟨z,hu hz⟩
      have hv : UpperHalfPlane.ofComplex z = v := UpperHalfPlane.ofComplex_apply_of_im_pos (hu hz)
      rw [hv]
      exact (primitive_hasDerivAt (f i) v).add_const (c i)
    have he (i : Fin g) : B.EqOn (ψ i) (fun w => primitive (f i) w + c i) := by
      apply (isOpen_ball : IsOpen B).eqOn_of_deriv_eq
        (𝕜 := ℂ) (f := ψ i) (g := fun w => primitive (f i) w + c i) (x := (t : ℂ))
        (convex_ball (t : ℂ) r).isPreconnected
      · exact fun z hz => (hψ i z hz).differentiableAt.differentiableWithinAt
      · exact fun z hz => (hP i z hz).differentiableAt.differentiableWithinAt
      · intro z hz
        exact (hψ i z hz).deriv.trans (hP i z hz).deriv.symm
      · exact ht
      · dsimp [c]
        abel
    have hread (x : UpperHalfPlane) (hx : (x : ℂ) ∈ B) : d x = q c := by
      have hv := hval (x : ℂ) hx
      rw [UpperHalfPlane.ofComplex_apply] at hv
      change a (quotientMap M x) - q (primitiveVector f x) = q c
      rw [← hv, ← map_sub]
      apply congrArg q
      funext i
      change ψ i (x : ℂ) - primitive (f i) (x : ℂ) = c i
      rw [he i hx]
      abel
    have hnear : ∀ᶠ x : UpperHalfPlane in 𝓝 t, (x : ℂ) ∈ B :=
      ((isOpen_ball : IsOpen B).preimage continuous_coe).eventually_mem ht
    exact hnear.mono fun x hx => (hread x hx).trans (hread t ht).symm
  have he := hl.apply_eq_of_preconnectedSpace τ UpperHalfPlane.I
  change a (quotientMap M τ) - q (primitiveVector f τ) =
    a (quotientMap M UpperHalfPlane.I) - q (primitiveVector f UpperHalfPlane.I) at he
  rw [primitive_I_vector, map_zero, sub_zero] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

/-- Pullback of the invariant first differential from the original
Abel map forces all its true modular deck periods into the kernel
of that same exponential. This derives the precise missing input to
the native quotient map, without building another target torus. -/
theorem periods_zero_of_original_lifts
    (f : Fin g → Form M) (q : (Fin g → ℂ) →+ J) (a : Base (image M) → J)
    (hLocal : LocalOriginalLifts f q a) (γ : image M) :
    q (modularPeriod f γ) = 0 := by
  have he := original_value_from_local_lifts f q a hLocal (γ • UpperHalfPlane.I)
  have hp : quotientMap M (γ • UpperHalfPlane.I) = quotientMap M UpperHalfPlane.I :=
    Quotient.sound (MulAction.orbitRel_apply.mpr ⟨γ,rfl⟩)
  rw [hp] at he
  change a (quotientMap M UpperHalfPlane.I) =
    q (modularPeriod f γ) + a (quotientMap M UpperHalfPlane.I) at he
  exact add_right_cancel (he.symm.trans (zero_add _).symm)

/-- Equality as an actual function on the same ordinary quotient. -/
theorem original_map_is_period_map
    (f : Fin g → Form M) (q : (Fin g → ℂ) →+ J) (a : Base (image M) → J)
    (hLocal : LocalOriginalLifts f q a) :
    a = fun x => ordinaryAbel f q (periods_zero_of_original_lifts f q a hLocal) x +
      a (quotientMap M UpperHalfPlane.I) := by
  funext x
  obtain ⟨t,rfl⟩ := GammaOneAtlas318.quotient_surjective M x
  rw [ordinaryAbel_value]
  exact original_value_from_local_lifts f q a hLocal t

end SelectedActualAbelPeriodAgreement318

#print axioms SelectedActualAbelPeriodAgreement318.periods_zero_of_original_lifts
#print axioms SelectedActualAbelPeriodAgreement318.original_map_is_period_map
