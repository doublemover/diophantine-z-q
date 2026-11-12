module
public import ThreeSelectedPolePreparation318
public section
noncomputable section
namespace SelectedPoleFullSource318
open CircuitReplay Raw318FinalReplay GeneratorScalarProgression318
open PreparedIntegerSource318 TwoTwistPointRealization318 ClearedContactForms318
open scoped Topology
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Same literal full288 source with all three preparation-zero pole inputs.
The finite selected-place trace input is still explicit; the actual ray1mod408
now supplies local squares and a constructed prior Q supplies all local depths.
No rational Realization or analytic prime-existence theorem is inferred. -/
theorem current_source (hglobal : ActualAnchorAllPlaces318.LocalGlobalPrinciple)
    (a : ℤ) (A B M : ℕ) (hM : 0<M) :
    ∃ J : ℕ, ∃ hJ : 0<J,
      ∀ d : ℕ, ∀ hd : d≠0,
        let d' := PreparedAnchorLabels318.multiplier (2^16) (J*d)
        let hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne (2^16) _
          (mul_ne_zero (Nat.ne_of_gt hJ) hd)
        let labels := FixedArithmeticLabels318.labels a A B d' hd'
        let C := construct labels
        ∀ T : ℕ, ∃ h₀ L : ℕ, ∃ N₂ N₃ N₁₇ : ℤ,
          T<h₀ ∧ 1<h₀ ∧ 0<L ∧ M∣L ∧ 64∣L ∧ 64∣h₀ ∧
          SourceLocalProgression318.Prepared 2 (a:ℚ) labels h₀ L N₂ 3 ∧
          SourceLocalProgression318.Prepared 3 (a:ℚ) labels h₀ L N₃ 1 ∧
          SourceLocalProgression318.Prepared 17 (a:ℚ) labels h₀ L N₁₇ 2 ∧
          ∃ threshold : ℚ, ∃ Q : ℕ, 0<Q ∧
          ∀ u w : ℤ, ∀ hp : MergedContactPrimePattern318.Values C u w,
            (Q:ℤ)∣w → (∀ k∈coefficients C, (408:ℤ)∣value u w k-1) →
            threshold≤parameter C u w →
          let Pi := MergedContactPrimePattern318.product C u w
          ∀ (Mminus Mplus Z : ℕ),
            0<Mminus → 0<Mplus →
            Nat.Coprime Pi Mplus → Nat.Coprime Pi L →
            Nat.Coprime Mminus Mplus → Nat.Coprime Mplus L → Nat.gcd Mminus L=16 →
          ∃ h : ℕ, Z<h ∧ Nat.ModEq (Pi^3*Mminus) h 0 ∧
            Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
            (1/100:ℝ)< |(normCoefficient (CoherentMultipleCharts318.chartU (h:ℤ)):ℝ)| ∧
            (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
              (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) ∧
            AllScalarSupportPreparation318.Prepared a labels h ∧
            let pre := ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) (parameter C u w)
            (∀ j : Fin 3, 0<pre (190+51*j.val) ∧ pre (190+51*j.val)<17) ∧
            (∀ j : Fin 3,
              Function.Injective (fun k => value u w (C.coefficient (j,k))) ∧
              (∀ k : Fin 5, Nat.Prime (value u w (C.coefficient (j,k))).natAbs ∧
                (value u w (C.coefficient (j,k))).natAbs∣Pi) ∧
              ∃ z : ℚ, z≠0 ∧ pre (190+51*j.val)=(rowProduct C u w j:ℚ)*z^2) ∧
            (SelectedContactDenominators318.SelectedTrace C (a:ℚ) (h:ℤ) u w hp →
              ThreeSelectedPolePreparation318.Prepared (a:ℚ) labels (h:ℤ) (parameter C u w)) ∧
            (0<scalarB (a:ℚ) labels (h:ℤ) ∧ scalarB (a:ℚ) labels (h:ℤ)<17) ∧
            (∀ P₀ : Realization (pre 190), ∀ P₁ : Realization (pre 241), ∀ P₂ : Realization (pre 292),
             ∀ P₃ : Realization (scalarB (a:ℚ) labels (h:ℤ)),
             HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)) := by
  obtain ⟨J,hJ,hprepare⟩ := ContactPrimeFullSource318.current_source hglobal a A B M hM
  refine ⟨J,hJ,?_⟩
  intro d hd
  dsimp only
  let d' := PreparedAnchorLabels318.multiplier (2^16) (J*d)
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne (2^16) _
    (mul_ne_zero (Nat.ne_of_gt hJ) hd)
  let labels := FixedArithmeticLabels318.labels a A B d' hd'
  let C := construct labels
  have hn : ∀ j, labels j≠0 := FixedArithmeticLabels318.labels_nonzero a A B d' hd'
  intro T
  obtain ⟨h₀,L,N₂,N₃,N₁₇,hbig,hone,hL,hML,h64L,h64h,h₂,h₃,h₁₇,threshold,ht⟩ := hprepare d hd T
  obtain ⟨Q,hQ,hfamily⟩ := ThreeSelectedPolePreparation318.family C hn (a:ℚ)
    h₀ L N₂ N₃ N₁₇ h₂ h₃ h₁₇
  refine ⟨h₀,L,N₂,N₃,N₁₇,hbig,hone,hL,hML,h64L,h64h,h₂,h₃,h₁₇,threshold,Q,hQ,?_⟩
  intro u w hp hw hray hlarge
  dsimp only
  intro Mm Mp Z hMm hMp hPm hPL hmp hpL hgcd
  obtain ⟨h,hZ,hprimary,hopposite,hcontinuity,hreal,hroots,hscalar,hpoles,hclasses,hscalarB,hfinish⟩ :=
    ht u w hp hlarge Mm Mp Z hMm hMp hPm hPL hmp hpL hgcd
  exact ⟨h,hZ,hprimary,hopposite,hcontinuity,hreal,hroots,hscalar,hpoles,hclasses,
    hfamily u w hp hw hray h hcontinuity hpoles,hscalarB,hfinish⟩

end SelectedPoleFullSource318
