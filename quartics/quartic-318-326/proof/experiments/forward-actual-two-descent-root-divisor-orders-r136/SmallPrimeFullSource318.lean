module
public import JointSmallPrimePreparation318
public section
noncomputable section
namespace SmallPrimeFullSource318
open Filter CircuitReplay Raw318FinalReplay GeneratorScalarProgression318
open PreparedIntegerSource318 ScalarSmallPrimeProgression318 SourceLocalProgression318
open TwoTwistPointRealization318
open scoped Topology
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Only scalar support primes outside the three actually prepared places
remain in the denominator criterion. The data are the original source leaves. -/
@[expose] def OtherSupport (a : ℤ) (labels : Fin 4 → ℤ) (h : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p≠2 → p≠3 → p≠17 →
    0<padicValRat p (114444*ScalarForwardWitness318.inputR (a:ℚ)) →
    padicValRat p (ScalarForwardWitness318.inputR (a:ℚ))<
      padicValRat p (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ) 37) ∧
    padicValRat p (ScalarForwardWitness318.inputR (a:ℚ))<
      padicValRat p (2*DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ) 33) ∧
    2*padicValRat p (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ) 37)+
      29*padicValRat p (ScalarForwardWitness318.inputR (a:ℚ))<
        2*padicValRat p (ActualScalarRoot318.inverseNorm (labels 1))

lemma scalar_denominator (a : ℤ) (labels : Fin 4 → ℤ)
    (hn : labels 1≠0) (hn1 : labels 1≠1) (h : ℕ) (hh : (h:ℤ)≠0)
    (hs : SmallPrepared a labels h) (hother : OtherSupport a labels h) :
    IsSquare (scalarB (a:ℚ) labels (h:ℤ)).den := by
  let w := DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)
  apply ScalarPolePreparation318.actual_square_denominator w (labels 1) a
    (DetectorGateWitness318.witness_input _ _ _) hs.1
  intro p hp hsupport
  by_cases h2 : p=2
  · subst p; exact hs.2.1
  by_cases h3 : p=3
  · subst p; exact hs.2.2.1
  by_cases h17 : p=17
  · subst p; exact hs.2.2.2.1
  letI : Fact p.Prime := ⟨hp⟩
  have hsp : 0<padicValRat p (114444*ScalarForwardWitness318.inputR (a:ℚ)) := by
    simpa only [DetectorGateWitness318.witness_input] using hsupport
  obtain ⟨hH,hf,hI⟩ := hother p hp h2 h3 h17 hsp
  have hH0 : w 37≠0 := by
    rw [ScalarActualInputs318.detector37]
    exact SeventeenScalarDepth318.norm_ne _ hh
  have hf0 : w 33≠0 := by
    rw [ScalarActualInputs318.detector33]
    exact SeventeenScalarDepth318.half_trace_ne _ hh
  have hr : ScalarForwardWitness318.inputR (w 0)≠0 := by
    rw [DetectorGateWitness318.witness_input]
    have he := ScalarForwardWitness318.integer_inputR_large a
    linarith
  exact (ScalarPackedLocalUnit318.actual_unit p w (labels 1) hr hf0 hH0 hn hn1
    (by simpa only [DetectorGateWitness318.witness_input] using hH)
    (by simpa only [DetectorGateWitness318.witness_input] using hf)
    (by simpa only [DetectorGateWitness318.witness_input] using hI)).2

/-- All constructed small-prime preparations meet the literal full288-row
consumer at the same final h. Prime-pattern compatibility, support primes
outside2/3/17, the four rational realizations, and the rational local-global
anchor principle remain individually explicit. -/
theorem current_source (hglobal : ActualAnchorAllPlaces318.LocalGlobalPrinciple)
    (a : ℤ) (A B : ℕ) (hA : 6≤A) :
    ∃ e : ℕ, ∀ d : ℕ, ∀ hd : d≠0,
      let d' := PreparedAnchorLabels318.multiplier (2^16) (20*17^e*d)
      let hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne (2^16) _
        (mul_ne_zero (by positivity) hd)
      let labels := FixedArithmeticLabels318.labels a A B d' hd'
      ∀ M T : ℕ, 0<M → ∃ (h₀ L : ℕ) (N₂ N₃ N₁₇ : ℤ),
        T<h₀ ∧ 1<h₀ ∧ 0<L ∧ M∣L ∧
        Prepared 2 (a:ℚ) labels h₀ L N₂ 3 ∧
        Prepared 3 (a:ℚ) labels h₀ L N₃ 1 ∧
        Prepared 17 (a:ℚ) labels h₀ L N₁₇ 2 ∧
        (∀ᶠ t : ℚ in atTop,
          ∀ Pi Mminus Mplus depth Z : ℕ,
          0<Pi → 0<Mminus → 0<Mplus →
          Nat.Coprime Pi Mplus → Nat.Coprime Pi L →
          Nat.Coprime Mminus Mplus → Nat.Coprime Mplus L → Nat.gcd Mminus L=16 →
          ∃ h : ℕ, Z<h ∧ Nat.ModEq (Pi^depth*Mminus) h 0 ∧
            Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
            (1/100:ℝ)< |(normCoefficient (CoherentMultipleCharts318.chartU (h:ℤ)):ℝ)| ∧
            (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
              (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) ∧
            SmallPrepared a labels h ∧
            let pre := ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) t
            (∀ j : Fin 3, 0<pre (190+51*j.val) ∧ pre (190+51*j.val)<17) ∧
            (0<scalarB (a:ℚ) labels (h:ℤ) ∧ scalarB (a:ℚ) labels (h:ℤ)<17) ∧
            (OtherSupport a labels h → IsSquare (scalarB (a:ℚ) labels (h:ℤ)).den) ∧
            (∀ P₀ : Realization (pre 190), ∀ P₁ : Realization (pre 241), ∀ P₂ : Realization (pre 292),
             ∀ P₃ : Realization (scalarB (a:ℚ) labels (h:ℤ)),
             HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ))) := by
  obtain ⟨e,he⟩ := JointSmallPrimePreparation318.integer_small_primes a A B (2^16) hA
  refine ⟨e,?_⟩
  intro d hd
  dsimp only
  have hd0 : 20*17^e*d≠0 := mul_ne_zero (by positivity) hd
  let d' := PreparedAnchorLabels318.multiplier (2^16) (20*17^e*d)
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne (2^16) _ hd0
  let labels := FixedArithmeticLabels318.labels a A B d' hd'
  obtain ⟨_,_,hlabels,_,hevent⟩ :=
    PreparedAllPlaceSource318.current_source_prepared_all_places hglobal a A B (20*17^e*d) hA hd0
  have hn : ∀ j, labels j≠0 := fun j => ne_of_gt (hlabels j).1
  have hn1 : labels 1≠1 := by
    have hs := (ScalarPreparedResidues318.label_domains A B d' hd').1
    change ScalarPreparedResidues318.scalarLabel A B d'≠1
    omega
  intro M T hM
  obtain ⟨h₀,L,N₂,N₃,N₁₇,hbig,hone,hL,hML,hmL,hres,hscalar,h₂,h₃,h₁₇⟩ := he d hd M T hM
  have h64m : 64∣ScalarPreparedResidues318.modulus A B := by
    have hp : (2:ℕ)^6∣2^A := pow_dvd_pow 2 hA
    change 64∣6*(2^A*3^B)
    exact hp.trans ((dvd_mul_right _ _).trans (dvd_mul_left _ _))
  have h64L := h64m.trans hmL
  have h64h := (ScalarPreparedResidues318.common_depths A B h₀ hA hres).2.1
  refine ⟨h₀,L,N₂,N₃,N₁₇,hbig,hone,hL,hML,h₂,h₃,h₁₇,?_⟩
  filter_upwards [hevent] with t ht
  intro Pi Mm Mp depth Z hPi hMm hMp hPm hPL hmp hpL hgcd
  obtain ⟨h,hlarge,hprimary,hopposite,hcontinuity,hreal,hroots,hpoles,hscalarB,_,_,_,hfinish⟩ :=
    ht Pi Mm Mp L h₀ depth Z hPi hMm hMp hL hPm hPL hmp hpL hgcd h64L h64h hmL hres
  have hs := hscalar h hcontinuity
  refine ⟨h,hlarge,hprimary,hopposite,hcontinuity,hreal,hroots,hs,hpoles,hscalarB,?_,hfinish⟩
  intro hother
  have hh : (h:ℤ)≠0 := by exact_mod_cast (show h≠0 by omega)
  exact scalar_denominator a labels (hn 1) hn1 h hh hs hother

end SmallPrimeFullSource318
