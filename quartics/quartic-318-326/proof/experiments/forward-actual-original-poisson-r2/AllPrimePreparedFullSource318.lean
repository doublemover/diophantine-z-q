module
public import AllScalarDetectorJoin318
public section
noncomputable section
namespace AllPrimePreparedFullSource318
open Filter CircuitReplay Raw318FinalReplay GeneratorScalarProgression318
open PreparedIntegerSource318 TwoTwistPointRealization318
open scoped Topology
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Same-index literal288-row consumer after actual scalar preparation at
EVERY support prime. Center, fixed labels, local thresholds and modulus are
constructed before contact parameter and final mixed CRT. No OtherSupport,
local unit, depth, center, or local recurrence premise remains. The exact
prime/order pattern, four rational two-twist Realizations and global anchor
principle remain explicit, as they must. -/
theorem current_source (hglobal : ActualAnchorAllPlaces318.LocalGlobalPrinciple)
    (a : ℤ) (A B M : ℕ) (hM : 0<M) :
    ∃ J : ℕ, ∃ hJ : 0<J,
      ∀ d : ℕ, ∀ hd : d≠0,
        let d' := PreparedAnchorLabels318.multiplier (2^16) (J*d)
        let hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne (2^16) _
          (mul_ne_zero (Nat.ne_of_gt hJ) hd)
        let labels := FixedArithmeticLabels318.labels a A B d' hd'
        ∀ T : ℕ, ∃ h₀ L : ℕ, ∃ N₂ N₃ N₁₇ : ℤ,
          T<h₀ ∧ 1<h₀ ∧ 0<L ∧ M∣L ∧ 64∣L ∧ 64∣h₀ ∧
          SourceLocalProgression318.Prepared 2 (a:ℚ) labels h₀ L N₂ 3 ∧
          SourceLocalProgression318.Prepared 3 (a:ℚ) labels h₀ L N₃ 1 ∧
          SourceLocalProgression318.Prepared 17 (a:ℚ) labels h₀ L N₁₇ 2 ∧
          ∀ᶠ t : ℚ in atTop,
          ∀ (Pi Mminus Mplus e Z : ℕ),
            0<Pi → 0<Mminus → 0<Mplus →
            Nat.Coprime Pi Mplus → Nat.Coprime Pi L →
            Nat.Coprime Mminus Mplus → Nat.Coprime Mplus L → Nat.gcd Mminus L=16 →
          ∃ h : ℕ, Z<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
            Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
            (1/100:ℝ)< |(normCoefficient (CoherentMultipleCharts318.chartU (h:ℤ)):ℝ)| ∧
            (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
              (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) ∧
            AllScalarSupportPreparation318.Prepared a labels h ∧
            let pre := ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) t
            (∀ j : Fin 3, 0<pre (190+51*j.val) ∧ pre (190+51*j.val)<17) ∧
            (0<scalarB (a:ℚ) labels (h:ℤ) ∧ scalarB (a:ℚ) labels (h:ℤ)<17) ∧
            (∀ P₀ : Realization (pre 190), ∀ P₁ : Realization (pre 241), ∀ P₂ : Realization (pre 292),
             ∀ P₃ : Realization (scalarB (a:ℚ) labels (h:ℤ)),
             HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)) := by
  obtain ⟨J,hJ,hprepare⟩ := AllScalarDetectorJoin318.integer_preparation a A B (2^16) M hM
  refine ⟨J,hJ,?_⟩
  intro d hd
  dsimp only
  let d' := PreparedAnchorLabels318.multiplier (2^16) (J*d)
  have hJd : J*d≠0 := mul_ne_zero (Nat.ne_of_gt hJ) hd
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne (2^16) _ hJd
  let labels := FixedArithmeticLabels318.labels a A B d' hd'
  have hn : ∀ j, labels j≠0 := FixedArithmeticLabels318.labels_nonzero a A B d' hd'
  have hn1 : labels 1≠1 := by
    have he := (ScalarPreparedResidues318.label_domains A B d' hd').1
    change ScalarPreparedResidues318.scalarLabel A B d'≠1
    omega
  have hhom := ActualAnchorAllPlaces318.actual_homogeneous hglobal a A B (2^16) (J*d) hJd
  have anchor := PhysicalAnchorFromHomogeneous318.currentAnchor labels hhom
  intro T
  obtain ⟨h₀,L,N₂,N₃,N₁₇,hbig,hone,hL,hML,h64L,h64h,hscalar,h₂,h₃,h₁₇⟩ := hprepare d hd T
  refine ⟨h₀,L,N₂,N₃,N₁₇,hbig,hone,hL,hML,h64L,h64h,h₂,h₃,h₁₇,?_⟩
  filter_upwards [PreparedTwistSource318.current_source_from_twists a labels hn hn1] with t ht
  intro Pi Mm Mp e Z hPi hMm hMp hPm hPL hmp hpL hgcd
  obtain ⟨h,hlarge,hprimary,hopposite,hcontinuity,hreal,hroots,hpoles,hscalarB,_,_,hfinish⟩ :=
    ht Pi Mm Mp L h₀ e Z hPi hMm hMp hL hPm hPL hmp hpL hgcd h64L h64h
  refine ⟨h,hlarge,hprimary,hopposite,hcontinuity,hreal,hroots,hscalar h hcontinuity,hpoles,hscalarB,?_⟩
  intro P₀ P₁ P₂ P₃
  exact hfinish P₀ P₁ P₂ P₃ anchor

end AllPrimePreparedFullSource318
