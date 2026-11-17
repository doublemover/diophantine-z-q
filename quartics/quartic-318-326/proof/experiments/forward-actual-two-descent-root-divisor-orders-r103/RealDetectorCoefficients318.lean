module
public import RealDetectorRatios318
public section
noncomputable section
namespace RealDetectorCoefficients318
open ActualCyclicClosure318 RealQuarticAmbient318 RealDetectorRatios318
open CircuitReplay
open scoped Topology
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def guard (labels : Fin 4 → ℤ) (j : Fin 4) (X : Pair) : ℝ :=
  re (fun e => (u labels (j.natAdd 4) e X)^2-(u labels (j.castAdd 4) e X)^2)
@[expose] def root (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2) (X : Pair) : ℝ :=
  (u labels (j.castAdd 4) e X*v labels (j.natAdd 4) e X+
    u labels (j.natAdd 4) e X*v labels (j.castAdd 4) e X)/
    ((u labels (j.natAdd 4) e X)^2-(u labels (j.castAdd 4) e X)^2)

/-- Real extension of the actual stored source coefficients before the
quadratic detector gates. Both embeddings share the same point X and labels. -/
@[expose] def raw (q : ℚ) (labels : Fin 4 → ℤ) (X : Pair) : ℕ → ℝ := fun i => match i with
  | 1 => re (fun e => u labels 0 e X)
  | 2 => im (fun e => u labels 0 e X)
  | 3 => re (fun e => v labels 0 e X)
  | 4 => im (fun e => v labels 0 e X)
  | 5 => re (fun e => u labels 1 e X)
  | 6 => im (fun e => u labels 1 e X)
  | 7 => re (fun e => v labels 1 e X)
  | 8 => im (fun e => v labels 1 e X)
  | 9 => re (fun e => u labels 2 e X)
  | 10 => im (fun e => u labels 2 e X)
  | 11 => re (fun e => v labels 2 e X)
  | 12 => im (fun e => v labels 2 e X)
  | 13 => re (fun e => u labels 3 e X)
  | 14 => im (fun e => u labels 3 e X)
  | 15 => re (fun e => v labels 3 e X)
  | 16 => im (fun e => v labels 3 e X)
  | 17 => re (fun e => u labels 4 e X)
  | 18 => im (fun e => u labels 4 e X)
  | 19 => re (fun e => v labels 4 e X)
  | 20 => im (fun e => v labels 4 e X)
  | 21 => re (fun e => u labels 5 e X)
  | 22 => im (fun e => u labels 5 e X)
  | 23 => re (fun e => v labels 5 e X)
  | 24 => im (fun e => v labels 5 e X)
  | 25 => re (fun e => u labels 6 e X)
  | 26 => im (fun e => u labels 6 e X)
  | 27 => re (fun e => v labels 6 e X)
  | 28 => im (fun e => v labels 6 e X)
  | 29 => re (fun e => u labels 7 e X)
  | 30 => im (fun e => u labels 7 e X)
  | 31 => re (fun e => v labels 7 e X)
  | 32 => im (fun e => v labels 7 e X)
  | 33 => re (fun e => (X e).val.1^2)
  | 34 => im (fun e => (X e).val.1^2)
  | 35 => re (fun e => shift e X)
  | 36 => im (fun e => shift e X)
  | 37 => re (fun e => (X e).val.1)^2-2*im (fun e => (X e).val.1)^2
  | 58 => re (fun e => (u labels 0 e X)^2)
  | 59 => re (fun e => u labels 0 e X)*im (fun e => u labels 0 e X)
  | 60 => re (fun e => (u labels 1 e X)^2)
  | 61 => re (fun e => u labels 1 e X)*im (fun e => u labels 1 e X)
  | 62 => re (fun e => (u labels 2 e X)^2)/2
  | 63 => re (fun e => u labels 2 e X)*im (fun e => u labels 2 e X)
  | 64 => re (fun e => (u labels 3 e X)^2)
  | 65 => re (fun e => u labels 3 e X)*im (fun e => u labels 3 e X)
  | 66 => re (fun e => (u labels 4 e X)^2)
  | 67 => re (fun e => u labels 4 e X)*im (fun e => u labels 4 e X)
  | 68 => re (fun e => (u labels 5 e X)^2)
  | 69 => re (fun e => u labels 5 e X)*im (fun e => u labels 5 e X)
  | 70 => re (fun e => (u labels 6 e X)^2)
  | 71 => re (fun e => u labels 6 e X)*im (fun e => u labels 6 e X)
  | 72 => re (fun e => (u labels 7 e X)^2)
  | 73 => re (fun e => u labels 7 e X)*im (fun e => u labels 7 e X)
  | 74 => re (fun e => (X e).val.1^2*shift e X)
  | 75 => im (fun e => (X e).val.1^2*shift e X)
  | 76 => re (fun e => fV e X)
  | 77 => im (fun e => fV e X)
  | 78 => (guard labels 0 X)⁻¹
  | 79 => re (fun e => root labels 0 e X)
  | 80 => im (fun e => root labels 0 e X)
  | 81 => (guard labels 1 X)⁻¹
  | 82 => re (fun e => root labels 1 e X)
  | 83 => im (fun e => root labels 1 e X)
  | 84 => (guard labels 2 X)⁻¹
  | 85 => re (fun e => root labels 2 e X)
  | 86 => im (fun e => root labels 2 e X)
  | 87 => (guard labels 3 X)⁻¹
  | 88 => re (fun e => root labels 3 e X)
  | 89 => im (fun e => root labels 3 e X)
  | 90 => re (fun e => (fV e X)^2)
  | 91 => re (fun e => fV e X)*im (fun e => fV e X)
  | 92 => re (fun e => Pade21Domains.PG (argument e X)/Pade21Domains.QG (argument e X))
  | 93 => im (fun e => Pade21Domains.PG (argument e X)/Pade21Domains.QG (argument e X))
  | 94 => re (fun e => common e X)
  | 95 => im (fun e => common e X)
  | 96 => re (fun e => alternatePolynomial labels 1 e X)
  | 97 => im (fun e => alternatePolynomial labels 1 e X)
  | 98 => re (fun e => alternatePolynomial labels 2 e X)
  | 99 => im (fun e => alternatePolynomial labels 2 e X)
  | 100 => re (fun e => alternatePolynomial labels 3 e X)
  | 101 => im (fun e => alternatePolynomial labels 3 e X)
  | 102 => re (fun e => primary labels 0 e X)
  | 103 => im (fun e => primary labels 0 e X)
  | 104 => re (fun e => alternate labels 0 e X)
  | 105 => im (fun e => alternate labels 0 e X)
  | 106 => re (fun e => primary labels 1 e X)
  | 107 => im (fun e => primary labels 1 e X)
  | 108 => re (fun e => alternate labels 1 e X)
  | 109 => im (fun e => alternate labels 1 e X)
  | 110 => re (fun e => primary labels 2 e X)
  | 111 => im (fun e => primary labels 2 e X)
  | 112 => re (fun e => alternate labels 2 e X)
  | 113 => im (fun e => alternate labels 2 e X)
  | 114 => re (fun e => primary labels 3 e X)
  | 115 => im (fun e => primary labels 3 e X)
  | 116 => re (fun e => alternate labels 3 e X)
  | 117 => im (fun e => alternate labels 3 e X)
  | _ => (q:ℝ)

@[expose] def value118 (w : ℕ → ℝ) : ℝ := -((-1 * w 0 * w 0))
@[fun_prop] lemma value118_continuous : Continuous value118 := by
  unfold value118
  fun_prop

@[expose] def value119 (w : ℕ → ℝ) : ℝ := -((-1 * w 106 * w 114) + (-2 * w 107 * w 115))
@[fun_prop] lemma value119_continuous : Continuous value119 := by
  unfold value119
  fun_prop

@[expose] def value120 (w : ℕ → ℝ) : ℝ := -((-1 * w 106 * w 115) + (-1 * w 107 * w 114))
@[fun_prop] lemma value120_continuous : Continuous value120 := by
  unfold value120
  fun_prop

@[expose] def value121 (w : ℕ → ℝ) : ℝ := -((-1 * w 106 * w 110) + (-2 * w 107 * w 111))
@[fun_prop] lemma value121_continuous : Continuous value121 := by
  unfold value121
  fun_prop

@[expose] def value122 (w : ℕ → ℝ) : ℝ := -((-1 * w 106 * w 111) + (-1 * w 107 * w 110))
@[fun_prop] lemma value122_continuous : Continuous value122 := by
  unfold value122
  fun_prop

@[expose] def value123 (w : ℕ → ℝ) : ℝ := -((-1 * w 110 * w 110) + (-2 * w 111 * w 111) + (-4 * w 114 * w 114) + (4 * w 114 * (value119 w)) + (-2 * w 114 * (value121 w)) + (-8 * w 115 * w 115) + (8 * w 115 * (value120 w)) + (-4 * w 115 * (value122 w)) + (-1 * (value119 w) * (value119 w)) + (1 * (value119 w) * (value121 w)) + (-2 * (value120 w) * (value120 w)) + (2 * (value120 w) * (value122 w)))
@[fun_prop] lemma value123_continuous : Continuous value123 := by
  unfold value123
  fun_prop

@[expose] def value124 (w : ℕ → ℝ) : ℝ := -((-1 * w 110 * w 111) + (-4 * w 114 * w 115) + (2 * w 114 * (value120 w)) + (-1 * w 114 * (value122 w)) + (2 * w 115 * (value119 w)) + (-1 * w 115 * (value121 w)) + (-1 * (value119 w) * (value120 w)) + ((1 / 2) * (value119 w) * (value122 w)) + ((1 / 2) * (value120 w) * (value121 w)))
@[fun_prop] lemma value124_continuous : Continuous value124 := by
  unfold value124
  fun_prop

@[expose] def value125 (w : ℕ → ℝ) : ℝ := -((-1 * w 90 * w 90) + (8 * w 91 * w 91))
@[fun_prop] lemma value125_continuous : Continuous value125 := by
  unfold value125
  fun_prop

@[expose] def value126 (w : ℕ → ℝ) : ℝ := -((-1 * w 37 * w 37))
@[fun_prop] lemma value126_continuous : Continuous value126 := by
  unfold value126
  fun_prop

@[expose] def value127 (w : ℕ → ℝ) : ℝ := -((-1 * w 102 * w 102) + (2 * w 102 * w 104) + (-2 * w 103 * w 103) + (-4 * w 103 * w 105) + (-1 * w 104 * w 104) + (-2 * w 105 * w 105))
@[fun_prop] lemma value127_continuous : Continuous value127 := by
  unfold value127
  fun_prop

@[expose] def value128 (w : ℕ → ℝ) : ℝ := -((-1 * w 102 * w 103) + (-1 * w 102 * w 105) + (1 * w 103 * w 104) + (1 * w 104 * w 105))
@[fun_prop] lemma value128_continuous : Continuous value128 := by
  unfold value128
  fun_prop

@[expose] def value129 (w : ℕ → ℝ) : ℝ := -((-1 * w 106 * w 106) + (2 * w 106 * w 108) + (-2 * w 107 * w 107) + (-4 * w 107 * w 109) + (-1 * w 108 * w 108) + (-2 * w 109 * w 109))
@[fun_prop] lemma value129_continuous : Continuous value129 := by
  unfold value129
  fun_prop

@[expose] def value130 (w : ℕ → ℝ) : ℝ := -((-1 * w 106 * w 107) + (-1 * w 106 * w 109) + (1 * w 107 * w 108) + (1 * w 108 * w 109))
@[fun_prop] lemma value130_continuous : Continuous value130 := by
  unfold value130
  fun_prop

@[expose] def value131 (w : ℕ → ℝ) : ℝ := -((-1 * w 110 * w 110) + (2 * w 110 * w 112) + (-2 * w 111 * w 111) + (-4 * w 111 * w 113) + (-1 * w 112 * w 112) + (-2 * w 113 * w 113))
@[fun_prop] lemma value131_continuous : Continuous value131 := by
  unfold value131
  fun_prop

@[expose] def value132 (w : ℕ → ℝ) : ℝ := -((-1 * w 110 * w 111) + (-1 * w 110 * w 113) + (1 * w 111 * w 112) + (1 * w 112 * w 113))
@[fun_prop] lemma value132_continuous : Continuous value132 := by
  unfold value132
  fun_prop

@[expose] def value133 (w : ℕ → ℝ) : ℝ := -((-1 * w 114 * w 114) + (2 * w 114 * w 116) + (-2 * w 115 * w 115) + (-4 * w 115 * w 117) + (-1 * w 116 * w 116) + (-2 * w 117 * w 117))
@[fun_prop] lemma value133_continuous : Continuous value133 := by
  unfold value133
  fun_prop

@[expose] def value134 (w : ℕ → ℝ) : ℝ := -((-1 * w 114 * w 115) + (-1 * w 114 * w 117) + (1 * w 115 * w 116) + (1 * w 116 * w 117))
@[fun_prop] lemma value134_continuous : Continuous value134 := by
  unfold value134
  fun_prop

@[expose] def value135 (w : ℕ → ℝ) : ℝ := -((-1 * w 0 * w 0) + ((1 / 7446) * w 0 * w 102) + (-2 * w 0 * (value118 w)) + ((-1 / 221771664) * w 102 * w 102) + ((1 / 7446) * w 102 * (value118 w)) + ((-1 / 110885832) * w 103 * w 103) + (-1 * (value118 w) * (value118 w)))
@[fun_prop] lemma value135_continuous : Continuous value135 := by
  unfold value135
  fun_prop

@[expose] def value136 (w : ℕ → ℝ) : ℝ := -((-1 * w 0 * w 103) + ((1 / 14892) * w 102 * w 103) + (-1 * w 103 * (value118 w)))
@[fun_prop] lemma value136_continuous : Continuous value136 := by
  unfold value136
  fun_prop

@[expose] def value137 (w : ℕ → ℝ) : ℝ := -((-1 * (value123 w) * (value123 w)) + (-8 * (value124 w) * (value124 w)))
@[fun_prop] lemma value137_continuous : Continuous value137 := by
  unfold value137
  fun_prop

@[expose] def value138 (w : ℕ → ℝ) : ℝ := -((-1 * (value123 w) * (value124 w)))
@[fun_prop] lemma value138_continuous : Continuous value138 := by
  unfold value138
  fun_prop

@[expose] def value139 (w : ℕ → ℝ) : ℝ := -((-1 * w 79 * w 82) + (-2 * w 80 * w 83))
@[fun_prop] lemma value139_continuous : Continuous value139 := by
  unfold value139
  fun_prop

@[expose] def value140 (w : ℕ → ℝ) : ℝ := -((-1 * w 79 * w 83) + (-1 * w 80 * w 82))
@[fun_prop] lemma value140_continuous : Continuous value140 := by
  unfold value140
  fun_prop

@[expose] def value141 (w : ℕ → ℝ) : ℝ := -((-1 * w 85 * (value139 w)) + (-2 * w 86 * (value140 w)))
@[fun_prop] lemma value141_continuous : Continuous value141 := by
  unfold value141
  fun_prop

@[expose] def value142 (w : ℕ → ℝ) : ℝ := -((-1 * w 85 * (value140 w)) + (-1 * w 86 * (value139 w)))
@[fun_prop] lemma value142_continuous : Continuous value142 := by
  unfold value142
  fun_prop

@[expose] def value143 (w : ℕ → ℝ) : ℝ := -((-1 * w 88 * (value141 w)) + (-2 * w 89 * (value142 w)))
@[fun_prop] lemma value143_continuous : Continuous value143 := by
  unfold value143
  fun_prop

@[expose] def value144 (w : ℕ → ℝ) : ℝ := -((-1 * w 88 * (value142 w)) + (-1 * w 89 * (value141 w)))
@[fun_prop] lemma value144_continuous : Continuous value144 := by
  unfold value144
  fun_prop

@[expose] def value145 (w : ℕ → ℝ) : ℝ := -((-1 * (value143 w) * (value143 w)) + (2 * (value144 w) * (value144 w)))
@[fun_prop] lemma value145_continuous : Continuous value145 := by
  unfold value145
  fun_prop

@[expose] def fill (w : ℕ → ℝ) : ℕ → ℝ := fun i => match i with
  | 118 => value118 w
  | 119 => value119 w
  | 120 => value120 w
  | 121 => value121 w
  | 122 => value122 w
  | 123 => value123 w
  | 124 => value124 w
  | 125 => value125 w
  | 126 => value126 w
  | 127 => value127 w
  | 128 => value128 w
  | 129 => value129 w
  | 130 => value130 w
  | 131 => value131 w
  | 132 => value132 w
  | 133 => value133 w
  | 134 => value134 w
  | 135 => value135 w
  | 136 => value136 w
  | 137 => value137 w
  | 138 => value138 w
  | 139 => value139 w
  | 140 => value140 w
  | 141 => value141 w
  | 142 => value142 w
  | 143 => value143 w
  | 144 => value144 w
  | 145 => value145 w
  | i => w i

@[expose] def coefficients (q : ℚ) (labels : Fin 4 → ℤ) (X : Pair) : ContactChainReal318.Coeff :=
  fun i => fill (raw q labels X) i.val

end RealDetectorCoefficients318
