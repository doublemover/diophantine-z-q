module
public import CircuitReplay
public section
namespace AffineAnchor
open CircuitReplay

@[expose] def forward (u v z : ℕ) (S : ℚ) (w : Assignment) : Assignment :=
  fun i => if i = u then S + (w u - 3*w v + 3*w z)/4
    else if i = v then S/2 + w v/4
    else if i = z then 3*S/2 + w z/4 else w i

@[expose] def backward (u v z : ℕ) (S : ℚ) (w : Assignment) : Assignment :=
  fun i => if i = u then 4*w u + 12*w v - 12*w z + 8*S
    else if i = v then 4*w v - 2*S
    else if i = z then 4*w z - 6*S else w i

theorem forward_backward (u v z : ℕ) (huv : u ≠ v) (huz : u ≠ z)
    (hvz : v ≠ z) (S : ℚ) (w : Assignment) :
    forward u v z S (backward u v z S w) = w := by
  funext i
  by_cases hi : i = u
  · subst i; simp [forward, backward, huv, huz, hvz, Ne.symm huv, Ne.symm huz, Ne.symm hvz]; ring
  · by_cases hj : i = v
    · subst i; simp [forward, backward, huv, huz, hvz, Ne.symm huv, Ne.symm huz, Ne.symm hvz]; ring
    · by_cases hk : i = z
      · subst i; simp [forward, backward, huv, huz, hvz, Ne.symm huv, Ne.symm huz, Ne.symm hvz]; ring
      · simp [forward, backward, hi, hj, hk]

theorem backward_forward (u v z : ℕ) (huv : u ≠ v) (huz : u ≠ z)
    (hvz : v ≠ z) (S : ℚ) (w : Assignment) :
    backward u v z S (forward u v z S w) = w := by
  funext i
  by_cases hi : i = u
  · subst i; simp [forward, backward, huv, huz, hvz, Ne.symm huv, Ne.symm huz, Ne.symm hvz]; ring
  · by_cases hj : i = v
    · subst i; simp [forward, backward, huv, huz, hvz, Ne.symm huv, Ne.symm huz, Ne.symm hvz]; ring
    · by_cases hk : i = z
      · subst i; simp [forward, backward, huv, huz, hvz, Ne.symm huv, Ne.symm huz, Ne.symm hvz]; ring
      · simp [forward, backward, hi, hj, hk]

theorem solutions (rows : List Row) (u v z : ℕ) (huv : u ≠ v) (huz : u ≠ z)
    (hvz : v ≠ z) (hu : u ≠ 0) (hv : v ≠ 0) (hz : z ≠ 0) (S q : ℚ) :
    HasSolution rows q ↔ HasSolution (rows.map (fun r => r ∘ forward u v z S)) q := by
  constructor
  · rintro ⟨w,hw,hs⟩
    refine ⟨backward u v z S w, ?_, ?_⟩
    · simpa [backward, Ne.symm hu, Ne.symm hv, Ne.symm hz] using hw
    · apply (constraints_map rows _ _).2
      simpa only [forward_backward u v z huv huz hvz] using hs
  · rintro ⟨w,hw,hs⟩
    refine ⟨forward u v z S w, ?_, (constraints_map rows _ _).1 hs⟩
    simpa [forward, Ne.symm hu, Ne.symm hv, Ne.symm hz] using hw

end AffineAnchor
