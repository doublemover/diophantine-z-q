module
public import ActualFourPoleClassMatching318
public section
noncomputable section
namespace ActualPoleSurfaceReduction318
open TwoTwistPointRealization318 ActualFourPoleClassMatching318

@[expose] def denominator (β k : ℚ) : ℚ := k^2+3*β
@[expose] def parameter (β k : ℚ) : ℚ := β*(k^2-β)/denominator β k

lemma denominator_ne (β k : ℚ) (hβ : 0<β) : denominator β k≠0 := by
  unfold denominator
  positivity

/-- A genuine rational first point in the prescribed actual squareclass.
The pole and its complement are not replaced; n is the free shared parameter. -/
def first (β k : ℚ) (hβ : 0<β) : SquareclassPoint β (parameter β k) where
  root := 1
  ordinate := 4*β^2*k/denominator β k
  root_ne := one_ne_zero
  equation := by
    have hd := denominator_ne β k hβ
    dsimp only [parameter]
    field_simp [hd]
    dsimp only [denominator]
    ring

/-- The remaining rational surface equation. A point on this surface is
an explicit input, not inferred from local preparation or positivity. -/
structure SurfacePoint (β θ : ℚ) where
  k : ℚ
  s : ℚ
  v : ℚ
  s_ne : s≠0
  equation : v^2=β*
    (denominator β k*s^2-(k^2-β)*θ)*
    (denominator β k*s^2+3*(k^2-β)*θ)

/-- A surface witness supplies the SECOND original elliptic point at the
same n as first; its rational ordinate and nonzero root are explicit. -/
def second {β θ : ℚ} (hβ : 0<β) (P : SurfacePoint β θ) :
    SquareclassPoint β (parameter β P.k*θ) where
  root := P.s
  ordinate := β*P.s*P.v/denominator β P.k
  root_ne := P.s_ne
  equation := by
    have hd := denominator_ne β P.k hβ
    calc
      (β*P.s*P.v/denominator β P.k)^2 =
          β^2*P.s^2*P.v^2/(denominator β P.k)^2 := by ring
      _ = β^2*P.s^2*(β*
          (denominator β P.k*P.s^2-(P.k^2-β)*θ)*
          (denominator β P.k*P.s^2+3*(P.k^2-β)*θ))/
          (denominator β P.k)^2 := by rw [P.equation]
      _ = (β*P.s^2)*(β*P.s^2-parameter β P.k*θ)*
          (β*P.s^2+3*(parameter β P.k*θ)) := by
        dsimp only [parameter]
        field_simp [hd]
        ring

/-- Conditional reduction at the ACTUAL b and C. There is no existence
assertion for SurfacePoint and no restriction n≠0 or ordinate≠0. -/
def matched (b C : ℚ) (hC : 0<C) (P : SurfacePoint (17*C) (1-b/17)) :
    MatchedPoints b C where
  n := parameter (17*C) P.k
  first := first (17*C) P.k (by positivity)
  second := second (by positivity) P

/-- Preserve both actual class equations through the existing exact factor
bridge. The unresolved surface witness stays visible in the telescope. -/
def realization (b C z : ℚ) (hb : 0<b) (hz : z≠0) (hf : b=C*z^2)
    (P : SurfacePoint (17*C) (1-b/17)) : Realization b := by
  have hC : 0<C := by
    have hs : 0<z^2 := sq_pos_of_ne_zero hz
    rw [hf] at hb
    exact (mul_pos_iff_of_pos_right hs).mp hb
  exact fromFactor b C z (ne_of_gt hb) hz hf (matched b C hC P)

end ActualPoleSurfaceReduction318
