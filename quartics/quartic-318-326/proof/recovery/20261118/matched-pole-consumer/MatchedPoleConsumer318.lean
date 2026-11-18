module
public import NormalizedPolePoints318
public section
noncomputable section
namespace MatchedPoleConsumer318
open NormalizedPolePoints318

def weight (β t : ℚ) : ℚ := 1 + 3 * β * t^2
def gain (β t : ℚ) : ℚ :=
  ((1 - β*t^2) * (1 - 9*β*t^2)) / (weight β t)^2
def ordinate (β u t : ℚ) : ℚ :=
  (8*β^2*u^3*t*(1-3*β*t^2)) / (weight β t)^2

theorem seed_equation (β u t : ℚ) (hw : weight β t ≠ 0) :
    (ordinate β u t)^2 = (β*u^2) * ((β*u^2) - (β*u^2)*gain β t) *
      ((β*u^2) + 3*((β*u^2)*gain β t)) := by
  unfold ordinate gain
  field_simp [hw] <;> simp only [weight] <;> ring

/-- A pair of matched rational seeds, at the actual b and common parameter. -/
def ofMatching (b β u t v S : ℚ)
    (hB : 17*b = β*u^2) (ht : weight β t ≠ 0) (hv : weight β v ≠ 0)
    (hS : S ≠ 0)
    (hm : gain β t * ((17*b)^2 * (1-b/17)) = S^2 * gain β v) :
    PointPair b where
  parameter := (17*b)*gain β t
  s := S
  y₁ := ordinate β u t
  y₂ := ordinate β (u*S) v
  s_ne := hS
  first := by
    rw [hB]
    exact seed_equation β u t ht
  second := by
    have he : ((17*b)*gain β t) * ((17*b)^2*(1-b/17)) =
        (β*(u*S)^2)*gain β v := by
      rw [mul_assoc,hm,hB]
      ring
    rw [mul_assoc (3:ℚ) ((17*b)*gain β t) ((17*b)^2*(1-b/17)),he,hB]
    convert seed_equation β (u*S) v hv using 1 <;> ring

def den (β k t : ℚ) : ℚ := 1 + β*k*t
def phi (β k t : ℚ) : ℚ := (t+k)/(den β k t)
def q₁ (β t : ℚ) : ℚ := 1 - 9*β*t^2
def q₂ (β k t : ℚ) : ℚ := (den β k t)^2 - 9*β*(t+k)^2
def numerator (β k t : ℚ) : ℚ :=
  weight β (phi β k t) * (den β k t)^2 * q₁ β t

private theorem phi_norm (β k t : ℚ) (hd : den β k t ≠ 0) :
    (1-β*(phi β k t)^2)*(den β k t)^2 = (1-β*k^2)*(1-β*t^2) := by
  unfold phi
  field_simp [hd] <;> simp only [den] <;> ring

private theorem phi_second (β k t : ℚ) (hd : den β k t ≠ 0) :
    (1-9*β*(phi β k t)^2)*(den β k t)^2 = q₂ β k t := by
  unfold phi q₂
  field_simp [hd] <;> ring

theorem cover_identity (β θ k t Z : ℚ) (hd : den β k t ≠ 0)
    (ht : weight β t ≠ 0) (hv : weight β (phi β k t) ≠ 0)
    (hz : Z^2 = θ*(1-β*k^2)*q₁ β t*q₂ β k t) :
    θ*gain β (phi β k t) * (numerator β k t)^2 =
      gain β t * (weight β t * Z)^2 := by
  calc
    _ = θ*((1-β*(phi β k t)^2)*(den β k t)^2)*
        ((1-9*β*(phi β k t)^2)*(den β k t)^2)*(q₁ β t)^2 := by
          unfold gain numerator
          field_simp [hv] <;> ring
    _ = _ := by
      rw [phi_norm β k t hd,phi_second β k t hd]
      unfold gain
      rw [mul_pow,hz]
      field_simp [ht] <;> simp only [q₁] <;> ring

/-- A rational point on the affine nondegenerate chart of the matched quartic
suffices for a PointPair. No rational point is asserted or selected by this definition. -/
def ofCover (b β θ u z k t Z : ℚ)
    (hB : 17*b = β*u^2) (hD : 1-b/17 = θ*z^2)
    (hb : 17*b ≠ 0) (hθ : θ ≠ 0) (hz : z ≠ 0)
    (hd : den β k t ≠ 0) (ht : weight β t ≠ 0)
    (hv : weight β (phi β k t) ≠ 0) (hq : q₁ β t ≠ 0) (hZ : Z ≠ 0)
    (hc : Z^2 = θ*(1-β*k^2)*q₁ β t*q₂ β k t) : PointPair b := by
  let S : ℚ := (17*b)*θ*z*numerator β k t/(weight β t*Z)
  have hn : numerator β k t ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hv (pow_ne_zero 2 hd)) hq
  have hs : S ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hb hθ) hz) hn) (mul_ne_zero ht hZ)
  apply ofMatching b β u t (phi β k t) S hB ht hv hs
  have hi := cover_identity β θ k t Z hd ht hv hc
  rw [hD]
  dsimp only [S]
  calc
    _ = ((17*b)^2*θ*z^2) * (gain β t * (weight β t*Z)^2) /
          (weight β t*Z)^2 := by field_simp [ht,hZ] <;> ring
    _ = _ := by rw [←hi]; field_simp [ht,hZ] <;> ring

def certificateOfCover (b β θ u z k t Z : ℚ)
    (hB : 17*b = β*u^2) (hD : 1-b/17 = θ*z^2)
    (hb : b ≠ 0) (hθ : θ ≠ 0) (hz : z ≠ 0)
    (hd : den β k t ≠ 0) (ht : weight β t ≠ 0)
    (hv : weight β (phi β k t) ≠ 0) (hq : q₁ β t ≠ 0) (hZ : Z ≠ 0)
    (hc : Z^2 = θ*(1-β*k^2)*q₁ β t*q₂ β k t) : Certificate b :=
  PointPair.certificate hb (ofCover b β θ u z k t Z hB hD (mul_ne_zero (by norm_num) hb)
    hθ hz hd ht hv hq hZ hc)

end MatchedPoleConsumer318
