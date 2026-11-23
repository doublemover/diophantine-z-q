module
public import AffineAnchor
public section
namespace AnchorValueShear
open CircuitReplay
set_option linter.unusedSimpArgs false

@[expose] def forward (u n : ℕ) (S : ℚ) (w : Assignment) : Assignment :=
  fun i => if i=u then w u-S*w n else if i=n then w n/4096 else w i

@[expose] def backward (u n : ℕ) (S : ℚ) (w : Assignment) : Assignment :=
  fun i => if i=u then w u+4096*S*w n else if i=n then 4096*w n else w i

theorem forward_backward (u n : ℕ) (hun : u ≠ n) (S : ℚ) (w : Assignment) :
    forward u n S (backward u n S w)=w := by
  funext i
  by_cases hu : i=u
  · subst i; simp [forward,backward,hun,Ne.symm hun]<;> ring
  · by_cases hn : i=n
    · subst i; simp [forward,backward,hun,Ne.symm hun]<;> ring
    · simp [forward,backward,hu,hn]

theorem backward_forward (u n : ℕ) (hun : u ≠ n) (S : ℚ) (w : Assignment) :
    backward u n S (forward u n S w)=w := by
  funext i
  by_cases hu : i=u
  · subst i; simp [forward,backward,hun,Ne.symm hun]<;> ring
  · by_cases hn : i=n
    · subst i; simp [forward,backward,hun,Ne.symm hun]<;> ring
    · simp [forward,backward,hu,hn]

theorem solutions (rows : List Row) (u n : ℕ) (hun : u ≠ n)
    (hu : u ≠ 0) (hn : n ≠ 0) (S q : ℚ) :
    HasSolution rows q ↔ HasSolution (rows.map (fun r => r ∘ forward u n S)) q := by
  constructor
  · rintro ⟨w,hw,hs⟩
    refine ⟨backward u n S w, ?_, ?_⟩
    · simpa [backward, Ne.symm hu,Ne.symm hn] using hw
    · apply (constraints_map rows _ _).2
      simpa only [forward_backward u n hun] using hs
  · rintro ⟨w,hw,hs⟩
    refine ⟨forward u n S w, ?_, (constraints_map rows _ _).1 hs⟩
    simpa [forward, Ne.symm hu,Ne.symm hn] using hw

end AnchorValueShear
