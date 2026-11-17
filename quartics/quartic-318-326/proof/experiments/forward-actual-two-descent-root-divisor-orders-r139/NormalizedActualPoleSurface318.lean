module
public import ActualPoleSurfaceReduction318
public section
noncomputable section
namespace NormalizedActualPoleSurface318
open TwoTwistPointRealization318 ActualPoleSurfaceReduction318

/-- Homogeneity of the explicit residual surface, with the same theta and
same nonzero second root. This is algebra, not point existence. -/
def rescale {β θ : ℚ} (μ : ℚ) (P : SurfacePoint β θ) :
    SurfacePoint (β*μ^2) θ where
  k := P.k*μ
  s := P.s
  v := P.v*μ^3
  s_ne := P.s_ne
  equation := by
    rw [mul_pow,P.equation]
    dsimp only [denominator]
    ring

/-- A single normalized surface witness at t=b/17 produces the exact
original Realization b. The pole b is unchanged, and no square root of17
or square root of b is requested. The two scales are the literal17 and17b. -/
def atActualPole (b : ℚ) (hb : 0<b)
    (P : SurfacePoint (b/17) (1-b/17)) : Realization b where
  β := b/17
  θ := 1-b/17
  c := 17
  d := 17*b
  n := parameter (b/17) P.k
  c_ne := by norm_num
  d_ne := mul_ne_zero (by norm_num) (ne_of_gt hb)
  first_class := by ring
  second_class := by ring
  first := first (b/17) P.k (by positivity)
  second := second (by positivity) P

/-- The coefficient-prime representative and the normalized surface are
connected by the ACTUAL nonzero factor z, not a replacement pole. -/
def fromNormalizedFactor (b C z : ℚ) (hb : 0<b) (hz : z≠0)
    (hf : b=C*z^2) (P : SurfacePoint (b/17) (1-b/17)) : Realization b := by
  have he : (b/17)*(17/z)^2=17*C := by
    rw [hf]
    field_simp [hz]
    ring
  have Q := rescale (17/z) P
  rw [he] at Q
  exact ActualPoleSurfaceReduction318.realization b C z hb hz hf Q

end NormalizedActualPoleSurface318
