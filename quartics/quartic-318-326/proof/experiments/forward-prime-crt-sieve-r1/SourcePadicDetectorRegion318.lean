module
public import PadicDetectorUniformPreparation318
public section
noncomputable section
namespace SourcePadicDetectorRegion318
open CircuitReplay PadicDetectorCoefficients318 ThreeDetectorArithmetic318
open ScaledContactWeights318 DetectorPrimeProduct318
open Set
set_option maxHeartbeats 1000000

/-- Before the common contact parameter and before the final h, construct a
nonempty p-adic neighborhood centered at the actual original h₀ coefficients.
Every later original orbit point whose coefficients remain in it satisfies
the same three small-prime preparations. No coefficient bound is supplied. -/
theorem exists_region (p : ℕ) [Fact p.Prime] (q : ℚ)
    (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) (h₀ : ℤ)
    (A : ℤ) (hA : 0≤A) :
    ∃ U : Set (Coeff ℚ_[p]), IsOpen U ∧
      project p (DetectorGateWitness318.witness q labels h₀)∈U ∧
      ∃ N : ℤ, ∀ (u d : ℚ), d≠0 → N≤padicValRat p d →
      ∀ h : ℤ, project p (DetectorGateWitness318.witness q labels h)∈U →
      ∀ (k : Fin 3 → Fin 5 → ℤ),
      (∀ j i, linear (scales labels j) u d i=(k j i:ℚ)) →
      (∀ j i, k j i≠0) → (∀ j i, padicValRat p (k j i:ℚ)=0) →
      (∀ j i, IsSquare (k j i:ℚ_[p])) →
      ∀ j : Fin 3,
        IsSquare ((ThreeDetectorUniformFamily318.witness q labels h (u/d^2) (190+51*j.val):ℚ):ℚ_[p]) ∧
        A≤padicValRat p (ThreeDetectorUniformFamily318.witness q labels h (u/d^2) (190+51*j.val)) := by
  obtain ⟨U,hU,hcenter,N,hN⟩ := PadicDetectorUniformPreparation318.three_scales p
    (DetectorGateWitness318.witness q labels h₀) (scales labels) (scales_ne labels hn) A hA
  refine ⟨U,hU,hcenter,N,?_⟩
  intro u d hd hdepth h hh k hk hkn hku hks j
  obtain ⟨_,_,hs,hv⟩ := hN u d hd hdepth (DetectorGateWitness318.witness q labels h)
    hh j (k j) (hk j) (hkn j) (hku j) (hks j)
  simpa only [stored_pole] using And.intro hs hv

/-- Exact remaining index-access task: producing a modulus which sends the
original residue progression into the already constructed coefficient region.
This statement names the input and is not a claimed producer of that modulus. -/
@[expose] def ProgressionAccess (p : ℕ) [Fact p.Prime] (q : ℚ)
    (labels : Fin 4 → ℤ) (h₀ L : ℕ) (U : Set (Coeff ℚ_[p])) : Prop :=
  0<L ∧ ∀ h : ℕ, Nat.ModEq L h h₀ →
    project p (DetectorGateWitness318.witness q labels (h:ℤ))∈U

end SourcePadicDetectorRegion318
