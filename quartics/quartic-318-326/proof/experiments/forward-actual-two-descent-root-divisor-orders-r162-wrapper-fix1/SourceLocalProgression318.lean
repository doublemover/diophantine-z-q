module
public import DetectorLocalRegularity318
public section
noncomputable section
namespace SourceLocalProgression318
open SourcePadicDetectorRegion318 PadicDetectorCoefficients318
open ScaledContactWeights318 DetectorPrimeProduct318 ThreeDetectorArithmetic318
set_option maxHeartbeats 1000000

/-- The formerly explicit source-access premise is produced from the actual
oriented orbit and the actual quotient domains at the chosen center. -/
theorem access (p : ℕ) [Fact p.Prime]
    (hb : ∀ a b h₀ : ℤ, LocalIndexRegularity318.Regular h₀
      (fun h => ActualOrbitLocalFilter318.error p (a+b*h)))
    (q : ℚ) (labels : Fin 4 → ℤ) (h₀ : ℕ) (hzero : (h₀:ℤ)≠0) (hone : (h₀:ℤ)≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels (h₀:ℤ)))
    (U : Set (Coeff ℚ_[p])) (hU : IsOpen U)
    (hc : project p (DetectorGateWitness318.witness q labels (h₀:ℤ))∈U) :
    ∃ L : ℕ, ProgressionAccess p q labels h₀ L U := by
  have hr := DetectorLocalRegularity318.project_regular p (h₀:ℤ) hb q labels hzero hone hg
  obtain ⟨E,hE,haccess⟩ := LocalIndexRegularity318.nat_progression hr U (hU.mem_nhds hc)
  exact ⟨E,hE,haccess⟩

/-- Literal three stored poles on one original progression. These are the
actual contact-factor hypotheses, not an assertion that the prime pattern or
its rational point realizations already exist. -/
@[expose] def Prepared (p : ℕ) [Fact p.Prime] (q : ℚ) (labels : Fin 4 → ℤ)
    (h₀ L : ℕ) (N A : ℤ) : Prop :=
  ∀ (u d : ℚ), d≠0 → N≤padicValRat p d →
    ∀ h : ℕ, Nat.ModEq L h h₀ → ∀ (k : Fin 3 → Fin 5 → ℤ),
    (∀ j i, linear (scales labels j) u d i=(k j i:ℚ)) →
    (∀ j i, k j i≠0) → (∀ j i, padicValRat p (k j i:ℚ)=0) →
    (∀ j i, IsSquare (k j i:ℚ_[p])) → ∀ j : Fin 3,
      IsSquare ((ThreeDetectorUniformFamily318.witness q labels (h:ℤ) (u/d^2)
        (190+51*j.val):ℚ):ℚ_[p]) ∧
      A≤padicValRat p (ThreeDetectorUniformFamily318.witness q labels (h:ℤ) (u/d^2)
        (190+51*j.val))

/-- The coefficient neighborhood, denominator threshold and congruence
modulus all precede u,d and the final h. Only the actual affine-chart regularity producer is used. -/
theorem prepared_progression (p : ℕ) [Fact p.Prime]
    (hb : ∀ a b h₀ : ℤ, LocalIndexRegularity318.Regular h₀
      (fun h => ActualOrbitLocalFilter318.error p (a+b*h)))
    (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (h₀ : ℕ) (hzero : (h₀:ℤ)≠0) (hone : (h₀:ℤ)≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels (h₀:ℤ)))
    (A : ℤ) (hA : 0≤A) :
    ∃ (L : ℕ) (N : ℤ), 0<L ∧ Prepared p q labels h₀ L N A := by
  obtain ⟨U,hU,hcenter,N,hN⟩ := exists_region p q labels hn (h₀:ℤ) A hA
  obtain ⟨E,hE,haccess⟩ := access p hb q labels h₀ hzero hone hg U hU hcenter
  refine ⟨E,N,hE,?_⟩
  intro u d hd hdepth h hh k hk hkn hku hks j
  exact hN u d hd hdepth (h:ℤ) (haccess h hh) k hk hkn hku hks j

lemma Prepared.of_dvd (p : ℕ) [Fact p.Prime] (q : ℚ) (labels : Fin 4 → ℤ)
    (h₀ L L' : ℕ) (N A : ℤ) (h : Prepared p q labels h₀ L N A) (hL : L∣L') :
    Prepared p q labels h₀ L' N A := by
  intro u d hd hdepth n hn
  exact h u d hd hdepth n (hn.of_dvd hL)

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
/-- Actual simultaneous source preparation at2 and3, including any fixed
previous modulus M. The same original q,labels,h and pole slots190/241/292
are consumed at both places. Prime17 remains a separate input. -/
theorem two_three (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (h₀ M : ℕ) (hM : 0<M) (hzero : (h₀:ℤ)≠0) (hone : (h₀:ℤ)≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels (h₀:ℤ))) :
    ∃ (L : ℕ) (N₂ N₃ : ℤ), 0<L ∧ M∣L ∧
      Prepared 2 q labels h₀ L N₂ 3 ∧ Prepared 3 q labels h₀ L N₃ 1 := by
  obtain ⟨E₂,N₂,hE₂,h₂⟩ := prepared_progression 2
    (LocalIndexRegularity318.actual_chart 2 ActualOrbitLocalFilter318.two_error_bound)
    q labels hn h₀ hzero hone hg 3 (by norm_num)
  obtain ⟨E₃,N₃,hE₃,h₃⟩ := prepared_progression 3
    (LocalIndexRegularity318.actual_chart 3 ActualOrbitLocalFilter318.three_error_bound)
    q labels hn h₀ hzero hone hg 1 (by norm_num)
  let L := M*(E₂*E₃)
  have hL₂ : E₂∣L := (dvd_mul_right E₂ E₃).trans (dvd_mul_left _ _)
  have hL₃ : E₃∣L := (dvd_mul_left E₃ E₂).trans (dvd_mul_left _ _)
  refine ⟨L,N₂,N₃,by dsimp [L]; positivity,dvd_mul_right _ _,?_,?_⟩
  · exact Prepared.of_dvd 2 q labels h₀ E₂ L N₂ 3 h₂ hL₂
  · exact Prepared.of_dvd 3 q labels h₀ E₃ L N₃ 1 h₃ hL₃

end SourceLocalProgression318
