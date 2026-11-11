module
public import ScalarIndexContinuity318
public section
noncomputable section
namespace ScalarSmallPrimeProgression318
open ScalarForwardWitness318
open ScalarPreparedResidues318 (modulus residue)
open SeventeenScalarCenter318 (center)
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

@[expose] def SmallPrepared (a : ℤ) (labels : Fin 4 → ℤ) (h : ℕ) : Prop :=
  let w := DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)
  W w (labels 1)≠0 ∧ padicValRat 2 (W w (labels 1))=0 ∧
    padicValRat 3 (W w (labels 1))=0 ∧ padicValRat 17 (W w (labels 1))=0 ∧
    padicValRat 2 (poleInput w (labels 1))=4 ∧
    padicValRat 3 (poleInput w (labels 1))=2 ∧
    padicValRat 17 (poleInput w (labels 1))=2 ∧
    IsSquare ((poleInput w (labels 1):ℚ):ℚ_[2]) ∧
    IsSquare ((poleInput w (labels 1):ℚ):ℚ_[3]) ∧
    IsSquare ((poleInput w (labels 1):ℚ):ℚ_[17])

/-- Actual fixed labels, actual common center and a genuine progression
produce every scalar small-prime condition. The free positive multiplier d
and arbitrary earlier modulus M remain available. No prime-pattern, guard,
point-realization or rational-anchor premise is used by this theorem. -/
theorem prepare (a : ℤ) (A B N : ℕ) (hA : 6≤A) :
    ∃ e : ℕ, ∀ d : ℕ, ∀ hd : d≠0,
      let d' := PreparedAnchorLabels318.multiplier N (20*17^e*d)
      let hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _
        (mul_ne_zero (by positivity) hd)
      let labels := FixedArithmeticLabels318.labels a A B d' hd'
      ∀ M : ℕ, 0<M → ∃ L : ℕ, 0<L ∧ M∣L ∧ modulus A B∣L ∧
        ∀ h : ℕ, Nat.ModEq L h (center A B) → SmallPrepared a labels h := by
  obtain ⟨e,he⟩ := SeventeenScalarCenter318.center_unit a A B N (by omega)
  refine ⟨e,?_⟩
  intro d hd
  dsimp only
  let d' := PreparedAnchorLabels318.multiplier N (20*17^e*d)
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _ (mul_ne_zero (by positivity) hd)
  let labels := FixedArithmeticLabels318.labels a A B d' hd'
  have hcenter := he d hd
  have hh : (center A B:ℤ)≠0 := by exact_mod_cast ne_of_gt (SeventeenScalarCenter318.center_positive A B)
  have hr : inputR (a:ℚ)≠0 := by have h := integer_inputR_large a; linarith
  have hreg := ScalarIndexContinuity318.actual 17 AllSmallPrimeProgression318.actual_chart
    (a:ℚ) labels (labels 1) (center A B:ℤ) hh hr
  obtain ⟨L₁₇,hL₁₇,haccess⟩ := ScalarIndexContinuity318.unit_progression 17
    (fun h => W (DetectorGateWitness318.witness (a:ℚ) labels h) (labels 1))
    (center A B) hreg hcenter.1 hcenter.2
  intro M hM
  let L := M*(modulus A B*L₁₇)
  have hLm : modulus A B∣L := (dvd_mul_right _ _).trans (dvd_mul_left _ _)
  have hL17 : L₁₇∣L := (dvd_mul_left _ _).trans (dvd_mul_left _ _)
  refine ⟨L,by dsimp [L]; exact Nat.mul_pos hM (Nat.mul_pos (ScalarPreparedResidues318.modulus_pos A B) hL₁₇),
    dvd_mul_right _ _,hLm,?_⟩
  intro h hc
  have h23 := FixedArithmeticLabels318.actual_units a A B d' h hA hd'
    ((hc.of_dvd hLm).trans (SeventeenScalarCenter318.center_congruence A B))
  have h17 := haccess h (hc.of_dvd hL17)
  have hpoles := ScalarSmallPrimePreparation318.actual_pole_thresholds
    (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1) a
    (DetectorGateWitness318.witness_input _ _ _) h17.1 h23.1 h23.2 h17.2
  have hsquares := ScalarLocalSquares318.actual_pole_squares
    (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1) a
    (DetectorGateWitness318.witness_input _ _ _)
  exact ⟨h17.1,h23.1,h23.2,h17.2,hpoles.1,hpoles.2.1,hpoles.2.2,hsquares.1,hsquares.2.1,hsquares.2.2⟩

end ScalarSmallPrimeProgression318
