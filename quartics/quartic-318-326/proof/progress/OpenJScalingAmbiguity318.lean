module
public import OpenJAnalyticPoints318
public section
noncomputable section
namespace OpenJScalingAmbiguity318
open OpenJComplexEvaluation318
set_option maxHeartbeats 0

lemma fiber_a4_ne_zero (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    (fiber N tau h).a₄ ≠ 0 := by
  rw [fiber_eq]
  change -3 * ActualQJ318.jInvariant tau * (ActualQJ318.jInvariant tau-1728)⁻¹ ≠ 0
  exact mul_ne_zero (mul_ne_zero (by norm_num) h.1) (inv_ne_zero (sub_ne_zero.mpr h.2))

lemma fiber_a6_ne_zero (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    (fiber N tau h).a₆ ≠ 0 := by
  rw [fiber_eq]
  change -2 * ActualQJ318.jInvariant tau * (ActualQJ318.jInvariant tau-1728)⁻¹ ≠ 0
  exact mul_ne_zero (mul_ne_zero (by norm_num) h.1) (inv_ne_zero (sub_ne_zero.mpr h.2))

/-- All permissible coordinate scalings for this actual arithmetic fiber
agree up to sign. The excluded j-values are precisely where this argument
would need the larger automorphism groups. -/
theorem scaling_eq_or_neg (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau)
    (u v : ℂˣ)
    (hu4 : (ModularWeierstrass318.curve tau).a₄ = (u:ℂ)^4 * (fiber N tau h).a₄)
    (hu6 : (ModularWeierstrass318.curve tau).a₆ = (u:ℂ)^6 * (fiber N tau h).a₆)
    (hv4 : (ModularWeierstrass318.curve tau).a₄ = (v:ℂ)^4 * (fiber N tau h).a₄)
    (hv6 : (ModularWeierstrass318.curve tau).a₆ = (v:ℂ)^6 * (fiber N tau h).a₆) :
    (u:ℂ) = v ∨ (u:ℂ) = -(v:ℂ) := by
  have h4 : (u:ℂ)^4=(v:ℂ)^4 := mul_right_cancel₀ (fiber_a4_ne_zero N tau h) (hu4.symm.trans hv4)
  have h6 : (u:ℂ)^6=(v:ℂ)^6 := mul_right_cancel₀ (fiber_a6_ne_zero N tau h) (hu6.symm.trans hv6)
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  apply mul_right_cancel₀ (pow_ne_zero 4 (Units.ne_zero u))
  calc
    (u:ℂ)^2*(u:ℂ)^4 = (u:ℂ)^6 := by ring
    _ = (v:ℂ)^6 := h6
    _ = (v:ℂ)^2*(v:ℂ)^4 := by ring
    _ = (v:ℂ)^2*(u:ℂ)^4 := by rw [h4]

/-- The corresponding point maps differ only by the genuine elliptic
negation, not by an arbitrary permutation of torsion labels. -/
theorem point_maps_eq_or_neg (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau)
    (u v : ℂˣ)
    (hu4 : (ModularWeierstrass318.curve tau).a₄ = (u:ℂ)^4 * (fiber N tau h).a₄)
    (hu6 : (ModularWeierstrass318.curve tau).a₆ = (u:ℂ)^6 * (fiber N tau h).a₆)
    (hv4 : (ModularWeierstrass318.curve tau).a₄ = (v:ℂ)^4 * (fiber N tau h).a₄)
    (hv6 : (ModularWeierstrass318.curve tau).a₆ = (v:ℂ)^6 * (fiber N tau h).a₆) :
    (∀ P, ShortScaling318.pointAddEquiv _ _ u hu4 hu6 P =
      ShortScaling318.pointAddEquiv _ _ v hv4 hv6 P) ∨
    (∀ P, ShortScaling318.pointAddEquiv _ _ u hu4 hu6 P =
      -ShortScaling318.pointAddEquiv _ _ v hv4 hv6 P) := by
  rcases scaling_eq_or_neg N tau h u v hu4 hu6 hv4 hv6 with he | he
  · left
    intro P
    cases P with
    | zero => rfl
    | some x y hx =>
      simp only [ShortScaling318.pointAddEquiv,ShortScaling318.pointEquiv,
        AddEquiv.coe_mk,Equiv.coe_fn_mk,ShortScaling318.pointMap,
        WeierstrassCurve.Affine.Point.mk,he]
  · right
    intro P
    cases P with
    | zero => rfl
    | some x y hx =>
      simp only [ShortScaling318.pointAddEquiv,ShortScaling318.pointEquiv,
        AddEquiv.coe_mk,Equiv.coe_fn_mk,ShortScaling318.pointMap,
        WeierstrassCurve.Affine.Point.mk,WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [he]; ring
      · simp only [WeierstrassCurve.Affine.negY,WeierstrassCurve.a₁_of_isShortNF,
          WeierstrassCurve.a₃_of_isShortNF]
        rw [he]; ring

end OpenJScalingAmbiguity318
