module
public import FiniteScalarCenter318
public section
noncomputable section
namespace AllScalarSupportPreparation318
open ScalarForwardWitness318
open scoped BigOperators
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Once the actual scalar label is fixed, one residue class preserves all
previously constructed units at a finite prime family. It retains any earlier
modulus, without requiring a detector guard domain at this early center. -/
theorem finite_unit_progression {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (a : ℤ) (labels : Fin 4 → ℤ) (h₀ M : ℕ) (hh : 0<h₀) (hM : 0<M)
    (hcenter : ∀ i, W (DetectorGateWitness318.witness (a:ℚ) labels (h₀:ℤ)) (labels 1)≠0 ∧
      padicValRat (p i) (W (DetectorGateWitness318.witness (a:ℚ) labels (h₀:ℤ)) (labels 1))=0) :
    ∃ L : ℕ, 0<L ∧ M∣L ∧ ∀ h : ℕ, Nat.ModEq L h h₀ → ∀ i,
      W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1)≠0 ∧
      padicValRat (p i) (W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1))=0 := by
  classical
  have hr : inputR (a:ℚ)≠0 := by have he := integer_inputR_large a; linarith
  have hh0 : (h₀:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt hh
  have he := fun i => ScalarIndexContinuity318.unit_progression (p i)
    (fun h => W (DetectorGateWitness318.witness (a:ℚ) labels h) (labels 1)) h₀
    (ScalarIndexContinuity318.actual (p i) (AllPrimeSourceProgression318.actual_chart (p i))
      (a:ℚ) labels (labels 1) (h₀:ℤ) hh0 hr) (hcenter i).1 (hcenter i).2
  choose L hL haccess using he
  let J := ∏ i, L i
  refine ⟨M*J,Nat.mul_pos hM (Finset.prod_pos (fun i _ => hL i)),dvd_mul_right _ _,?_⟩
  intro h hc i
  exact haccess i h (hc.of_dvd
    ((Finset.dvd_prod_of_mem L (Finset.mem_univ i)).trans (dvd_mul_left J M)))

@[expose] def Prepared (a : ℤ) (labels : Fin 4 → ℤ) (h : ℕ) : Prop :=
  let w := DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)
  ScalarSmallPrimeProgression318.SmallPrepared a labels h ∧
    IsSquare (poleInput w (labels 1)).den ∧
    ∀ p : ℕ, p.Prime → 0<padicValRat p (114444*inputR (a:ℚ)) →
      padicValRat p (W w (labels 1))=0

/-- Exact finite support coverage turns the constructed units into the
actual scalar square denominator and all required small-prime pole data. -/
theorem prepared_of_units (a : ℤ) (labels : Fin 4 → ℤ) (h : ℕ)
    (hu : ∀ i : RationalScalarSupport318.Index (114444*inputR (a:ℚ)),
      W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1)≠0 ∧
      padicValRat i.val (W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1))=0) :
    Prepared a labels h := by
  let w := DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)
  have hin : w 0=(a:ℚ) := DetectorGateWitness318.witness_input _ _ _
  have h2 := hu ⟨2,RationalScalarSupport318.two_mem _⟩
  have h3 := hu ⟨3,RationalScalarSupport318.three_mem _⟩
  have h17 := hu ⟨17,RationalScalarSupport318.seventeen_mem _⟩
  have hs : ∀ p : ℕ, p.Prime → 0<padicValRat p (114444*inputR (a:ℚ)) →
      padicValRat p (W w (labels 1))=0 := by
    intro p hp hv
    have hr : 114444*inputR (a:ℚ)≠0 := by
      have he := integer_inputR_large a
      positivity
    exact (hu ⟨p,RationalScalarSupport318.positive_mem _ hr p hp hv⟩).2
  have hpoles := ScalarSmallPrimePreparation318.actual_pole_thresholds w (labels 1) a hin
    h2.1 h2.2 h3.2 h17.2
  have hsquares := ScalarLocalSquares318.actual_pole_squares w (labels 1) a hin
  refine ⟨⟨h2.1,h2.2,h3.2,h17.2,hpoles.1,hpoles.2.1,hpoles.2.2,
    hsquares.1,hsquares.2.1,hsquares.2.2⟩,?_,hs⟩
  exact ScalarPolePreparation318.actual_square_denominator w (labels 1) a hin h2.1
    (fun p hp hv => hs p hp (by simpa only [hin] using hv))

/-- The entire scalar support-prime preparation is produced. The genuine
common center precedes J; J precedes the fixed Lucas/root labels; their actual
unit neighborhood then determines L. The free positive multiplier d remains
available. There is no OtherSupport inequality premise. -/
theorem integer_preparation (a : ℤ) (A B N M : ℕ) (hM : 0<M) :
    ∃ h₀ J : ℕ, ∃ hJ : 0<J, 0<h₀ ∧ 64∣h₀ ∧ M∣h₀ ∧
      ∀ d : ℕ, ∀ hd : d≠0,
        let d' := PreparedAnchorLabels318.multiplier N (J*d)
        let hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _
          (mul_ne_zero (Nat.ne_of_gt hJ) hd)
        let labels := FixedArithmeticLabels318.labels a A B d' hd'
        ∃ L : ℕ, 0<L ∧ 64∣L ∧ M∣L ∧
          ∀ h : ℕ, Nat.ModEq L h h₀ → Prepared a labels h := by
  let I := RationalScalarSupport318.Index (114444*inputR (a:ℚ))
  obtain ⟨h₀,J,hJ,hh,h64,hMdiv,hcenter⟩ :=
    FiniteScalarCenter318.center_units (fun i : I => i.val) a A B N M hM
  refine ⟨h₀,J,hJ,hh,h64,hMdiv,?_⟩
  intro d hd
  dsimp only
  let d' := PreparedAnchorLabels318.multiplier N (J*d)
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _ (mul_ne_zero (Nat.ne_of_gt hJ) hd)
  let labels := FixedArithmeticLabels318.labels a A B d' hd'
  obtain ⟨L,hL,hretain,haccess⟩ := finite_unit_progression (fun i : I => i.val)
    a labels h₀ (64*M) hh (by positivity) (hcenter d hd)
  refine ⟨L,hL,(dvd_mul_right 64 M).trans hretain,(dvd_mul_left M 64).trans hretain,?_⟩
  intro h hc
  exact prepared_of_units a labels h (haccess h hc)

end AllScalarSupportPreparation318
