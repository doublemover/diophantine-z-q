module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Tactic.Ring
public section
noncomputable section

namespace SelectedGeneralizedJCurve318

variable {R : Type*} [CommRing R]

/-- Actual denominator-normalized model over the full noncollision
j-line. Both J and J−1728 will be units; neither 2 nor 3 is inverted. -/
@[expose] def curve (d : Rˣ) : WeierstrassCurve R :=
  ⟨1,0,0,-36*(↑d⁻¹ : R),-(↑d⁻¹ : R)⟩

theorem c4_raw (d : Rˣ) : (curve d).c₄ = 1+1728*(↑d⁻¹ : R) := by
  simp only [curve,WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]
  ring

theorem delta_raw (d : Rˣ) :
    (curve d).Δ = (1+1728*(↑d⁻¹ : R))^2 * (↑d⁻¹ : R) := by
  simp only [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

theorem literal_times_inverse (J : R) (d : Rˣ) (hd : (d:R) = J-1728) :
    J*(↑d⁻¹ : R) = 1+1728*(↑d⁻¹ : R) := by
  have hJ : J=(d:R)+1728 := by rw [hd]; ring
  rw [hJ,add_mul]
  have he : (d:R)*(↑d⁻¹ : R) = 1 := by simp
  rw [he]

theorem c4_literal (J : R) (d : Rˣ) (hd : (d:R) = J-1728) :
    (curve d).c₄ = J*(↑d⁻¹ : R) :=
  (c4_raw d).trans (literal_times_inverse J d hd).symm

theorem delta_literal (J : R) (d : Rˣ) (hd : (d:R) = J-1728) :
    (curve d).Δ = J^2*(↑d⁻¹ : R)^3 := by
  rw [delta_raw,← literal_times_inverse J d hd]
  ring

theorem isElliptic (J : R) (d : Rˣ) (hd : (d:R) = J-1728) (hJ : IsUnit J) :
    (curve d).IsElliptic := by
  refine ⟨?_⟩
  rw [delta_literal J d hd]
  exact (hJ.pow 2).mul ((d⁻¹).isUnit.pow 3)

theorem j_literal (J : R) (d : Rˣ) (hd : (d:R) = J-1728) [(curve d).IsElliptic] :
    (curve d).j = J := by
  rw [WeierstrassCurve.j,Units.inv_mul_eq_iff_eq_mul,WeierstrassCurve.coe_Δ',
    c4_literal J d hd,delta_literal J d hd]
  ring

end SelectedGeneralizedJCurve318

#print axioms SelectedGeneralizedJCurve318.delta_literal
#print axioms SelectedGeneralizedJCurve318.j_literal
