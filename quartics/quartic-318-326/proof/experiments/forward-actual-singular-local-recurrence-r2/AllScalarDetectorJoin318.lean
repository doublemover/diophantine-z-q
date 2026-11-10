module
public import AllScalarSupportPreparation318
public section
noncomputable section
namespace AllScalarDetectorJoin318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Adjust the center AFTER fixing all labels while preserving every actual
scalar support-prime unit, then build the three original detector neighborhoods
there. One later modulus retains all preparations and the required64 factor. -/
theorem join (a : ℤ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (hbase Lbase T : ℕ) (hLbase : 0<Lbase) (h64L : 64∣Lbase) (h64h : 64∣hbase)
    (hscalar : ∀ h : ℕ, Nat.ModEq Lbase h hbase → AllScalarSupportPreparation318.Prepared a labels h) :
    ∃ h₀ L : ℕ, ∃ N₂ N₃ N₁₇ : ℤ,
      T<h₀ ∧ 1<h₀ ∧ 0<L ∧ Lbase∣L ∧ 64∣L ∧ 64∣h₀ ∧
      (∀ h : ℕ, Nat.ModEq L h h₀ → AllScalarSupportPreparation318.Prepared a labels h) ∧
      SourceLocalProgression318.Prepared 2 (a:ℚ) labels h₀ L N₂ 3 ∧
      SourceLocalProgression318.Prepared 3 (a:ℚ) labels h₀ L N₃ 1 ∧
      SourceLocalProgression318.Prepared 17 (a:ℚ) labels h₀ L N₁₇ 2 := by
  obtain ⟨h₀,hbig,hone,hcong,hguard,_⟩ :=
    JointSmallPrimePreparation318.adjust_center labels hn hbase Lbase T hLbase
  obtain ⟨L,N₂,N₃,N₁₇,hL,hdiv,h₂,h₃,h₁₇⟩ :=
    AllSmallPrimeProgression318.simultaneous (a:ℚ) labels hn h₀ Lbase hLbase
      (by exact_mod_cast (show h₀≠0 by omega))
      (by exact_mod_cast (show h₀≠1 by omega)) hguard
  have hh64 : 64∣h₀ := Nat.modEq_zero_iff_dvd.mp
    ((hcong.of_dvd h64L).trans (Nat.modEq_zero_iff_dvd.mpr h64h))
  refine ⟨h₀,L,N₂,N₃,N₁₇,hbig,hone,hL,hdiv,h64L.trans hdiv,hh64,?_,h₂,h₃,h₁₇⟩
  intro h hc
  exact hscalar h ((hc.of_dvd hdiv).trans hcong)

/-- All scalar support-prime units, admissible center, local detector
thresholds and common modulus are now constructed before contact/prime data.
The actual anchor3-power and the free scalar multiplier remain unchanged. -/
theorem integer_preparation (a : ℤ) (A B N M : ℕ) (hM : 0<M) :
    ∃ J : ℕ, ∃ hJ : 0<J,
      ∀ d : ℕ, ∀ hd : d≠0,
        let d' := PreparedAnchorLabels318.multiplier N (J*d)
        let hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _
          (mul_ne_zero (Nat.ne_of_gt hJ) hd)
        let labels := FixedArithmeticLabels318.labels a A B d' hd'
        ∀ T : ℕ, ∃ h₀ L : ℕ, ∃ N₂ N₃ N₁₇ : ℤ,
          T<h₀ ∧ 1<h₀ ∧ 0<L ∧ M∣L ∧ 64∣L ∧ 64∣h₀ ∧
          (∀ h : ℕ, Nat.ModEq L h h₀ → AllScalarSupportPreparation318.Prepared a labels h) ∧
          SourceLocalProgression318.Prepared 2 (a:ℚ) labels h₀ L N₂ 3 ∧
          SourceLocalProgression318.Prepared 3 (a:ℚ) labels h₀ L N₃ 1 ∧
          SourceLocalProgression318.Prepared 17 (a:ℚ) labels h₀ L N₁₇ 2 := by
  obtain ⟨hbase,J,hJ,hh,h64,hMbase,hprepare⟩ :=
    AllScalarSupportPreparation318.integer_preparation a A B N M hM
  refine ⟨J,hJ,?_⟩
  intro d hd
  dsimp only
  let d' := PreparedAnchorLabels318.multiplier N (J*d)
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _ (mul_ne_zero (Nat.ne_of_gt hJ) hd)
  let labels := FixedArithmeticLabels318.labels a A B d' hd'
  have hn : ∀ j, labels j≠0 := FixedArithmeticLabels318.labels_nonzero a A B d' hd'
  obtain ⟨Lbase,hLbase,h64L,hML,hscalar⟩ := hprepare d hd
  intro T
  obtain ⟨h₀,L,N₂,N₃,N₁₇,hbig,hone,hL,hretain,h64L',h64h,hscalar',h₂,h₃,h₁₇⟩ :=
    join a labels hn hbase Lbase T hLbase h64L h64 hscalar
  exact ⟨h₀,L,N₂,N₃,N₁₇,hbig,hone,hL,hML.trans hretain,h64L',h64h,hscalar',h₂,h₃,h₁₇⟩

end AllScalarDetectorJoin318
