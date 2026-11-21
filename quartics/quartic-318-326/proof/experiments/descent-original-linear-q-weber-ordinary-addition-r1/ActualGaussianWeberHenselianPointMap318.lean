module
public import ActualGaussianWeberHenselianAffineLift318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Valuation.ValuationSubring
public section
noncomputable section

namespace ActualGaussianWeberHenselianPointMap318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianAffineLift318

/-- The literal Weber model; the integral and residual coefficient is a₄=−1. -/
@[expose] def curve (K : Type*) [CommRing K] : WeierstrassCurve K := ⟨0,0,0,-1,0⟩

abbrev WP (K : Type*) [CommRing K] := (curve K).toAffine.Point

theorem literal_equation {K : Type*} [CommRing K] (x y : K) :
    (curve K).toAffine.Equation x y ↔ y^2=x^3-x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curve,toAffine,sub_eq_add_neg]

theorem discr_exact (K : Type*) [CommRing K] : (curve K).Δ=(64:K) := by
  norm_num [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]

theorem nonsing_of_equation {K : Type*} [Field K] (h2 : (2:K) ≠ 0)
    {x y : K} (he : y^2=x^3-x) : (curve K).toAffine.Nonsingular x y := by
  have hD : (curve K).Δ ≠ 0 := by
    rw [discr_exact,←show (2:K)^6=64 by norm_num]
    exact pow_ne_zero _ h2
  exact ((curve K).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hD).mp
    ((literal_equation x y).mpr he)

variable {F : Type*} [Field F] (V : ValuationSubring F)

theorem integral_square {z : F} (hz : z^2 ∈ V) : z ∈ V := by
  by_cases h0 : z=0
  · simpa only [h0] using V.zero_mem
  rcases V.mem_or_inv_mem z with h | h
  · exact h
  have hm := V.mul_mem (z^2) (z⁻¹) hz h
  have hE : z^2*z⁻¹=z := by rw [pow_two,mul_assoc,mul_inv_cancel₀ h0,mul_one]
  rwa [hE] at hm

theorem integral_y {x y : F} (he : y^2=x^3-x) (hx : x ∈ V) : y ∈ V := by
  apply integral_square V
  rw [he]
  exact sub_mem (pow_mem hx 3) hx

theorem equation_in_subring (a b : V)
    (h : V.subtype b^2 = V.subtype a^3-V.subtype a) : b^2=a^3-a := by
  apply V.subtype_injective
  simpa only [map_pow,map_sub] using h

theorem equation_in_residue (a b : V) (h : b^2=a^3-a) :
    residue V b^2=residue V a^3-residue V a := by
  simpa only [map_pow,map_sub] using congrArg (residue V) h

@[expose] def finiteReduction (h2 : (2:ResidueField V) ≠ 0)
    {x y : F} (h : y^2=x^3-x) (hx : x ∈ V) : WP (ResidueField V) :=
  let a : V := ⟨x,hx⟩
  let b : V := ⟨y,integral_y V h hx⟩
  Point.some (residue V a) (residue V b)
    (nonsing_of_equation h2 (equation_in_residue V a b (equation_in_subring V a b h)))

/-- Actual same-place point reduction, not an assumed hom.
For nonintegral x the special point is O. -/
@[expose] def specialize (h2 : (2:ResidueField V) ≠ 0) (P : WP F) : WP (ResidueField V) := by
  classical
  exact match P with
  | Point.zero => Point.zero
  | Point.some x y h =>
    if hx : x ∈ V then finiteReduction V h2 ((literal_equation x y).mp h.1) hx else Point.zero

theorem specialize_some_eq_zero (h2 : (2:ResidueField V) ≠ 0) {x y : F}
    (h : (curve F).toAffine.Nonsingular x y) :
    specialize V h2 (Point.some x y h) = Point.zero ↔ x ∉ V := by
  classical
  by_cases hx : x ∈ V
  · simp [specialize,hx,finiteReduction]
  · simp [specialize,hx]

/-- Surjectivity of the actual point reduction uses the exact hosted green
two-branch Henselian affine lifting, including y₀=0. -/
theorem specialize_surjective [HenselianLocalRing V] (hF : (2:F) ≠ 0)
    (h2 : (2:ResidueField V) ≠ 0) : Function.Surjective (specialize V h2) := by
  classical
  intro P
  cases P with
  | zero => exact ⟨Point.zero,rfl⟩
  | some x y hn =>
    obtain ⟨a,b,he,ha,hb⟩ := affine_lift h2 x y ((literal_equation x y).mp hn.1)
    have h : (V.subtype b)^2=(V.subtype a)^3 - V.subtype a := by
      simpa only [map_pow,map_sub] using congrArg V.subtype he
    refine ⟨Point.some (V.subtype a) (V.subtype b) (nonsing_of_equation hF h),?_⟩
    have haV : V.subtype a ∈ V := a.property
    simp only [specialize,dif_pos haV,finiteReduction]
    have ea : (⟨V.subtype a,haV⟩ : V)=a := Subtype.ext rfl
    have eb : (⟨V.subtype b,integral_y V h haV⟩ : V)=b := Subtype.ext rfl
    have hd : ∀ (x' y' : ResidueField V), ∀ h' : (curve (ResidueField V)).toAffine.Nonsingular x' y',
        x'=x → y'=y → Point.some x' y' h'=Point.some x y hn := by
      intro x' y' h' hx hy
      subst x'
      subst y'
      rfl
    exact hd _ _ _ (by rw [ea,ha]) (by rw [eb,hb])

end ActualGaussianWeberHenselianPointMap318
