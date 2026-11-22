module
public import FiveContactMetricBounds318

/-! Exact lower bound for the *weighted, unchanged* four-contact curvature
quotient in the +11 comparison. The old unweighted five-contact metric U
is not substituted. On the bounded region each closed real interval is
proved from the endpoints; no radius or argument is sampled. -/
public section
noncomputable section
namespace SelectedActualSameACurvature64

@[expose] def cubic (a b c d : ℝ) : ℝ := 960*(b*c*d + a*c*d + (1/7)*a*b*d + (1/80)*a*b*c)
@[expose] def cross (a b c d : ℝ) : ℝ :=
  32^2*c*d + (343^2/7)*b*d + (76832^2/80)*b*c +
  (375^2/7)*a*d + (76800^2/80)*a*c + (77175^2/560)*a*b
@[expose] def N (a b c d : ℝ) : ℝ := cubic a b c d + cross a b c d
@[expose] def U (a b c d : ℝ) : ℝ := 960 + a + b + c/7 + d/80
@[expose] def a (z : ℂ) := ‖z‖
@[expose] def b (z : ℂ) := ‖z-(32:ℂ)‖
@[expose] def c (z : ℂ) := ‖z-(-343:ℂ)‖
@[expose] def d (z : ℂ) := ‖z-(76832:ℂ)‖
@[expose] def metricU (z : ℂ) := U (a z) (b z) (c z) (d z)
@[expose] def curvatureRatio (z : ℂ) := N (a z) (b z) (c z) (d z) / (2*(metricU z)^3)

private theorem cubic_mono {a b c d A B C D : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D) :
    cubic a b c d ≤ cubic A B C D := by
  unfold cubic
  have hA0 : 0 ≤ A := ha0.trans ha
  have hB0 : 0 ≤ B := hb0.trans hb
  have hC0 : 0 ≤ C := hc0.trans hc
  have hD0 : 0 ≤ D := hd0.trans hd
  gcongr

private theorem N_mono {a b c d A B C D : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D) :
    N a b c d ≤ N A B C D := by
  apply add_le_add (cubic_mono ha0 hb0 hc0 hd0 ha hb hc hd)
  unfold cross
  have hA0 : 0 ≤ A := ha0.trans ha
  have hB0 : 0 ≤ B := hb0.trans hb
  have hC0 : 0 ≤ C := hc0.trans hc
  have hD0 : 0 ≤ D := hd0.trans hd
  gcongr

def low (x y h : ℝ) := max 0 (max (x-h) (h-y))
private theorem low_nonneg (x y h : ℝ) : 0 ≤ low x y h := le_max_left _ _

private theorem contact_bounds (z k : ℂ) {x y : ℝ} (hx : x ≤ ‖z‖) (hy : ‖z‖ ≤ y) :
    low x y ‖k‖ ≤ ‖z-k‖ ∧ ‖z-k‖ ≤ y+‖k‖ := by
  have h₁ := norm_sub_norm_le z k
  have h₂ := norm_sub_norm_le k z
  rw [norm_sub_rev] at h₂
  have hup : ‖z‖ + ‖k‖ ≤ y + ‖k‖ := by linarith only [hy]
  exact ⟨max_le (norm_nonneg _) (max_le (by linarith) (by linarith)),
    (norm_sub_le z k).trans hup⟩

def upper (y : ℝ) := U y (y+32) (y+343) (y+76832)
def Valid (x y : ℝ) := 128*(upper y)^3 ≤
    N (low x y 0) (low x y 32) (low x y 343) (low x y 76832)

private theorem cell (z : ℂ) (x y : ℝ) (hx : x ≤ ‖z‖) (hy : ‖z‖ ≤ y) (h : Valid x y) :
    128*(metricU z)^3 ≤ N (a z) (b z) (c z) (d z) := by
  have h0 := contact_bounds z (0:ℂ) hx hy
  have h1 := contact_bounds z (32:ℂ) hx hy
  have h2 := contact_bounds z (-343:ℂ) hx hy
  have h3 := contact_bounds z (76832:ℂ) hx hy
  norm_num at h0 h1 h2 h3
  have A : low x y 0 ≤ a z := by simpa [a] using h0.1
  have B : low x y 32 ≤ b z ∧ b z ≤ y+32 := by simpa [b] using h1
  have C : low x y 343 ≤ c z ∧ c z ≤ y+343 := by simpa [c] using h2
  have D : low x y 76832 ≤ d z ∧ d z ≤ y+76832 := by simpa [d] using h3
  have hU : metricU z ≤ upper y := by
    unfold metricU upper U a
    linarith [B.2,C.2,D.2]
  have hU0 : 0 ≤ metricU z := by unfold metricU U a b c d; positivity
  calc
    _ ≤ 128*(upper y)^3 := by gcongr
    _ ≤ _ := h
    _ ≤ _ := N_mono (low_nonneg _ _ _) (low_nonneg _ _ _) (low_nonneg _ _ _) (low_nonneg _ _ _)
      A B.1 C.1 D.1

private theorem bounded (z : ℂ) (hz : ‖z‖ ≤ 1000000) :
    128*(metricU z)^3 ≤ N (a z) (b z) (c z) (d z) := by
  by_cases h7 : ‖z‖ ≤ 7
  · exact cell z 0 7 (norm_nonneg z) h7 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h15 : ‖z‖ ≤ 15
  · exact cell z 7 15 (le_of_not_ge h7) h15 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h22 : ‖z‖ ≤ 22
  · exact cell z 15 22 (le_of_not_ge h15) h22 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h30 : ‖z‖ ≤ 30
  · exact cell z 22 30 (le_of_not_ge h22) h30 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h61 : ‖z‖ ≤ 61
  · exact cell z 30 61 (le_of_not_ge h30) h61 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h122 : ‖z‖ ≤ 122
  · exact cell z 61 122 (le_of_not_ge h61) h122 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h244 : ‖z‖ ≤ 244
  · exact cell z 122 244 (le_of_not_ge h122) h244 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h305 : ‖z‖ ≤ 305
  · exact cell z 244 305 (le_of_not_ge h244) h305 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h335 : ‖z‖ ≤ 335
  · exact cell z 305 335 (le_of_not_ge h305) h335 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h366 : ‖z‖ ≤ 366
  · exact cell z 335 366 (le_of_not_ge h335) h366 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h488 : ‖z‖ ≤ 488
  · exact cell z 366 488 (le_of_not_ge h366) h488 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h976 : ‖z‖ ≤ 976
  · exact cell z 488 976 (le_of_not_ge h488) h976 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h1953 : ‖z‖ ≤ 1953
  · exact cell z 976 1953 (le_of_not_ge h976) h1953 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h3906 : ‖z‖ ≤ 3906
  · exact cell z 1953 3906 (le_of_not_ge h1953) h3906 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h7812 : ‖z‖ ≤ 7812
  · exact cell z 3906 7812 (le_of_not_ge h3906) h7812 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h15625 : ‖z‖ ≤ 15625
  · exact cell z 7812 15625 (le_of_not_ge h7812) h15625 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h31250 : ‖z‖ ≤ 31250
  · exact cell z 15625 31250 (le_of_not_ge h15625) h31250 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h46875 : ‖z‖ ≤ 46875
  · exact cell z 31250 46875 (le_of_not_ge h31250) h46875 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h62500 : ‖z‖ ≤ 62500
  · exact cell z 46875 62500 (le_of_not_ge h46875) h62500 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h70312 : ‖z‖ ≤ 70312
  · exact cell z 62500 70312 (le_of_not_ge h62500) h70312 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h78125 : ‖z‖ ≤ 78125
  · exact cell z 70312 78125 (le_of_not_ge h70312) h78125 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h85937 : ‖z‖ ≤ 85937
  · exact cell z 78125 85937 (le_of_not_ge h78125) h85937 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h93750 : ‖z‖ ≤ 93750
  · exact cell z 85937 93750 (le_of_not_ge h85937) h93750 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h101562 : ‖z‖ ≤ 101562
  · exact cell z 93750 101562 (le_of_not_ge h93750) h101562 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h109375 : ‖z‖ ≤ 109375
  · exact cell z 101562 109375 (le_of_not_ge h101562) h109375 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h125000 : ‖z‖ ≤ 125000
  · exact cell z 109375 125000 (le_of_not_ge h109375) h125000 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h140625 : ‖z‖ ≤ 140625
  · exact cell z 125000 140625 (le_of_not_ge h125000) h140625 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h156250 : ‖z‖ ≤ 156250
  · exact cell z 140625 156250 (le_of_not_ge h140625) h156250 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h171875 : ‖z‖ ≤ 171875
  · exact cell z 156250 171875 (le_of_not_ge h156250) h171875 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h187500 : ‖z‖ ≤ 187500
  · exact cell z 171875 187500 (le_of_not_ge h171875) h187500 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h218750 : ‖z‖ ≤ 218750
  · exact cell z 187500 218750 (le_of_not_ge h187500) h218750 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h250000 : ‖z‖ ≤ 250000
  · exact cell z 218750 250000 (le_of_not_ge h218750) h250000 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h281250 : ‖z‖ ≤ 281250
  · exact cell z 250000 281250 (le_of_not_ge h250000) h281250 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h312500 : ‖z‖ ≤ 312500
  · exact cell z 281250 312500 (le_of_not_ge h281250) h312500 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h343750 : ‖z‖ ≤ 343750
  · exact cell z 312500 343750 (le_of_not_ge h312500) h343750 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h375000 : ‖z‖ ≤ 375000
  · exact cell z 343750 375000 (le_of_not_ge h343750) h375000 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h437500 : ‖z‖ ≤ 437500
  · exact cell z 375000 437500 (le_of_not_ge h375000) h437500 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h500000 : ‖z‖ ≤ 500000
  · exact cell z 437500 500000 (le_of_not_ge h437500) h500000 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h562500 : ‖z‖ ≤ 562500
  · exact cell z 500000 562500 (le_of_not_ge h500000) h562500 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h625000 : ‖z‖ ≤ 625000
  · exact cell z 562500 625000 (le_of_not_ge h562500) h625000 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h687500 : ‖z‖ ≤ 687500
  · exact cell z 625000 687500 (le_of_not_ge h625000) h687500 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h750000 : ‖z‖ ≤ 750000
  · exact cell z 687500 750000 (le_of_not_ge h687500) h750000 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  by_cases h875000 : ‖z‖ ≤ 875000
  · exact cell z 750000 875000 (le_of_not_ge h750000) h875000 (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])
  exact cell z 875000 1000000 (le_of_not_ge h875000) hz (by norm_num [Valid,upper,U,low,max_def,N,cubic,cross])

private theorem tail (z : ℂ) (hz : 1000000 ≤ ‖z‖) :
    128*(metricU z)^3 ≤ N (a z) (b z) (c z) (d z) := by
  let r := ‖z‖
  have rr : 0 ≤ r := norm_nonneg z
  have hh (k : ℂ) (hk : ‖k‖ ≤ 76832) :
      (9/10:ℝ)*r ≤ ‖z-k‖ ∧ ‖z-k‖ ≤ r+‖k‖ :=
    ⟨by dsimp [r]; linarith [norm_sub_norm_le z k],norm_sub_le z k⟩
  have B : (9/10:ℝ)*r ≤ b z ∧ b z ≤ r+32 := by
    simpa [b] using hh (32:ℂ) (by norm_num)
  have C : (9/10:ℝ)*r ≤ c z ∧ c z ≤ r+343 := by
    simpa [c] using hh (-343:ℂ) (by norm_num)
  have D : (9/10:ℝ)*r ≤ d z ∧ d z ≤ r+76832 := by
    simpa [d] using hh (76832:ℂ) (by norm_num)
  have hU : metricU z ≤ (11/5:ℝ)*r := by
    change 960 + r + b z + c z/7 + d z/80 ≤ _
    change 1000000 ≤ r at hz
    linarith [B.2,C.2,D.2]
  have hU0 : 0 ≤ metricU z := by unfold metricU U a b c d; positivity
  let m := (9/10:ℝ)*r
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hmA : m ≤ a z := by change (9/10:ℝ)*r ≤ r; linarith
  calc
    _ ≤ 128*((11/5:ℝ)*r)^3 := by gcongr
    _ ≤ cubic m m m m := by
      dsimp [cubic,m]
      ring_nf
      linarith only [pow_nonneg rr 3]
    _ ≤ cubic (a z) (b z) (c z) (d z) := cubic_mono hm hm hm hm hmA B.1 C.1 D.1
    _ ≤ N (a z) (b z) (c z) (d z) := by
      apply le_add_of_nonneg_right
      unfold cross a b c d
      positivity

theorem curvatureRatio_at_least_64 (z : ℂ) : 64 ≤ curvatureRatio z := by
  have hU : 0 < metricU z := by unfold metricU U a b c d; positivity
  apply (le_div_iff₀ (show 0 < 2*(metricU z)^3 by positivity)).2
  have h := (le_total ‖z‖ 1000000).elim (bounded z) (tail z)
  linarith only [h]

theorem sourceU_lower (z : ℂ) : 2 * max 32 ‖z‖ ≤ metricU z := by
  have hb := norm_sub_norm_le z (32:ℂ)
  norm_num at hb
  have hc : 0 ≤ c z := norm_nonneg _
  have hd : 0 ≤ d z := norm_nonneg _
  have hb0 : 0 ≤ b z := norm_nonneg _
  rcases le_total ‖z‖ (32:ℝ) with h|h
  · rw [max_eq_left h]
    unfold metricU U a
    linarith [norm_nonneg z]
  · rw [max_eq_right h]
    change 2 * ‖z‖ ≤ 960 + ‖z‖ + ‖z-(32:ℂ)‖ + c z/7 + d z/80
    linarith

end SelectedActualSameACurvature64
