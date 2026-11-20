module
public import ThetaFreeSelectedCut318
public import FixedTupleHeightGate318
import all CleanSparseHeightCut318
import all FixedTupleHeightGate318
public section
noncomputable section

namespace ThetaFreeFixedTupleSoundness318
open ContactHeight318 ThetaFreeSelectedCut318

/-- These are numerical consequences to be supplied by the selected CM
geometry, not a definition or certificate of complex multiplication. -/
def CMEstimates (u v : ℤ) : Prop :=
  ∃ hA : ℝ, pointHeight u v ≤ 2*(hA+Real.log Real.pi)+Real.log (540225/4 : ℝ) ∧
    hA < 854*support u v

/-- Numerical consequences of the actual non-CM geometry; g is the signed
Jacobian's dimension, n the Hom rank, delta the absolute descent degree, deg
the chosen isogeny's degree, b the quotient height, hY the target height.
No existence is asserted here. The two occurrences of b agree. -/
def SignedEstimates (u v : ℤ) : Prop :=
  ∃ g n delta deg b hY : ℝ,
    1 ≤ g ∧ g ≤ (support u v)^5 ∧ 1 ≤ n ∧ n ≤ 8*g ∧
    Real.log delta ≤ Real.log 576 + 3*n*Real.log 2 + 2*n*(1+Real.log n)*Real.log (n+1) ∧
    b ≤ 6*g*Real.log (support u v) ∧
    pointHeight u v ≤ 2*hY+Real.log (540225/4 : ℝ) ∧
    hY ≤ b+(1/2)*Real.log deg ∧ 0 < delta ∧ 0 < deg ∧
    deg ≤ (CMIsogeny318.Xi delta (b-Real.log Real.pi))^2

theorem cutoff {u v : ℤ} (h : CMEstimates u v ∨ SignedEstimates u v) :
    pointHeight u v < (support u v)^6/2 := by
  rcases h with ⟨hA,hb,hc⟩ | ⟨g,n,delta,deg,b,hY,hg,hgen,hn,hr,desc,rows,hh,hv,hd,he,hgr⟩
  · exact ThetaFreeSelectedCut318.cm hb hc
  · exact ThetaFreeSelectedCut318.from_signed_rows hg hgen hn hr desc rows hh hv hd he hgr

/-- Real.log 2 > 1/2 excludes the actual integer threshold; no implication
from the coarse cutoff to the older sharp S² log S budget is needed. -/
theorem excludes {u v : ℤ} (hc : IsCoprime u v)
    (hh : pointHeight u v < (support u v)^6/2) : ¬ CleanSparseHeightCut318.Extreme u v := by
  intro e
  let k : ℕ := (CleanSparseHeightCut318.S u v)^6
  change (2:ℕ)^k < CleanSparseHeightCut318.size u v at e
  have hle : ((2:ℕ)^k:ℝ) < (CleanSparseHeightCut318.size u v:ℝ) := by exact_mod_cast e
  have hl := Real.log_lt_log (by positivity : 0<((2:ℕ)^k:ℝ)) hle
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hl
  dsimp [k] at hl
  push_cast at hl
  change pointHeight u v < ((CleanSparseHeightCut318.S u v:ℕ):ℝ)^6/2 at hh
  have hhalf : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hhalf
    (pow_nonneg (Nat.cast_nonneg (CleanSparseHeightCut318.S u v) : 0≤((CleanSparseHeightCut318.S u v:ℕ):ℝ)) 6)
  nlinarith only [CleanSparseHeightCut318.height_log hc,hh,hl,hm]

/-- Estimates only at the one physical point selected from the specified tail,
and only if the original counterexample guards have actually been proved. -/
def AtSelected (a b c q : ℚ) : Prop := ∀ p : ℤ×ℤ,
  FixedTupleHeightGate318.first a b c q = some p → FixedTupleHeightGate318.CounterAt p →
  CMEstimates p.1 p.2 ∨ SignedEstimates p.1 p.2

private theorem impossible {a b c q : ℚ} {p : ℤ×ℤ} (H : AtSelected a b c q)
    (hp : FixedTupleHeightGate318.first a b c q = some p)
    (ob : FixedTupleHeightGate318.CounterAt p) : False :=
  excludes ob.2.1 (cutoff (H p hp ob)) ob.1

theorem tail318 (q : ℚ) (w : Fin 317 → ℚ)
    (hz : MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q w) Current318FinalPolynomial.P = 0)
    (H : AtSelected (w 37) (w 193) (w 244) q) : ∃ z : ℤ, (z:ℚ) = q := by
  by_contra ni
  obtain ⟨p,hp,ob⟩ := FixedTupleHeightGate318.counter318 q w hz ni
  exact impossible H hp ob

theorem tail326 (q : ℚ) (w : Fin 325 → ℚ)
    (hz : MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q w)
      Current326CoefficientBinding.tablePolynomial = 0)
    (H : AtSelected (w 37) (w 193) (w 244) q) : ∃ z : ℤ, (z:ℚ) = q := by
  by_contra ni
  obtain ⟨p,hp,ob⟩ := FixedTupleHeightGate318.counter326 q w hz ni
  exact impossible H hp ob

end ThetaFreeFixedTupleSoundness318
