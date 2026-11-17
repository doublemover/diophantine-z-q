module
public import ActualOriginalFiniteFourierEnergy318
public section
noncomputable section
namespace ActualOriginalQuadraticFourthMoment318
open MeasureTheory ActualOriginalFiniteFourierEnergy318
open ActualOriginalQuadraticEnergyCount318 IntegerResidueBoxCount318
open scoped BigOperators ComplexConjugate

@[expose] def quadraticSum (s : Finset ℤ) (c : ℤ) (θ : AddCircle (1 : ℝ)) : ℂ :=
  frequencySum s (fun n => c*n^2) θ
@[expose] def pairFrequency (c : ℤ) (p : ℤ×ℤ) : ℤ := c*p.1^2-c*p.2^2

/-- Exact fourth moment for any finite original integer interval or
subset. Repeated quadratic frequencies are counted with multiplicity. -/
theorem actual_quadratic_fourth_moment (s : Finset ℤ) (c : ℤ) :
    (∫ θ : AddCircle (1 : ℝ), ‖quadraticSum s c θ‖^4 ∂haarAddCircle)=
      ((frequencyEnergy (s.product s) (pairFrequency c)).card : ℝ) := by
  have he (θ : AddCircle (1 : ℝ)) : ‖quadraticSum s c θ‖^4=
      ‖frequencySum (s.product s) (pairFrequency c) θ‖^2 := by
    rw [show frequencySum (s.product s) (pairFrequency c) θ=
      quadraticSum s c θ*conj (quadraticSum s c θ) from (actual_frequency_difference s (fun n => c*n^2) θ).symm]
    simp only [norm_mul,Complex.norm_conj]
    ring
  simp_rw [he]
  exact actual_frequency_second_moment _ _

/-- Inject every actual finite collision into the original bounded
integer difference-of-squares energy. Nonzero c cancels exactly; no
coprimality or positivity of this signed coefficient is required. -/
@[expose] def energyEmbedding (H : ℕ) (s : Finset ℤ)
    (hs : s⊆Finset.Icc (-(H : ℤ)) H) (c : ℤ) (hc : c≠0)
    (p : ↥(frequencyEnergy (s.product s) (pairFrequency c))) : Energy H := by
  have hp := Finset.mem_filter.mp p.2
  have hl := Finset.mem_product.mp (Finset.mem_product.mp hp.1).1
  have hr := Finset.mem_product.mp (Finset.mem_product.mp hp.1).2
  refine ⟨((⟨p.1.1.1,hs hl.1⟩,⟨p.1.1.2,hs hl.2⟩),
    (⟨p.1.2.1,hs hr.1⟩,⟨p.1.2.2,hs hr.2⟩)),?_⟩
  have hh : c*(p.1.1.1^2-p.1.1.2^2)=c*(p.1.2.1^2-p.1.2.2^2) := by
    simpa only [mul_sub,pairFrequency] using hp.2
  exact mul_left_cancel₀ hc hh

lemma actual_energyEmbedding_injective (H : ℕ) (s : Finset ℤ)
    (hs : s⊆Finset.Icc (-(H : ℤ)) H) (c : ℤ) (hc : c≠0) :
    Function.Injective (energyEmbedding H s hs c hc) := by
  intro p q he
  apply Subtype.ext
  exact congrArg (fun z : Energy H => ((z.1.1.1.1,z.1.1.2.1),(z.1.2.1.1,z.1.2.2.1))) he

/-- Uniform fourth moment for ALL actual bounded subsets/prefixes and
ALL nonzero signed coefficients. No maximal-prefix moment is asserted. -/
theorem actual_bounded_quadratic_fourth_moment (H : ℕ) (s : Finset ℤ)
    (hs : s⊆Finset.Icc (-(H : ℤ)) H) (c : ℤ) (hc : c≠0)
    (δ : ℝ) (hδ : 0<δ) :
    (∫ θ : AddCircle (1 : ℝ), ‖quadraticSum s c θ‖^4 ∂haarAddCircle)≤momentBudget H δ := by
  rw [actual_quadratic_fourth_moment]
  have hh := Nat.card_le_card_of_injective (energyEmbedding H s hs c hc)
    (actual_energyEmbedding_injective H s hs c hc)
  have hb : ((frequencyEnergy (s.product s) (pairFrequency c)).card : ℝ)≤Nat.card (Energy H) := by
    exact_mod_cast (show (frequencyEnergy (s.product s) (pairFrequency c)).card≤Nat.card (Energy H) by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hh)
  exact hb.trans (actual_quadratic_energy_count H δ hδ)

end ActualOriginalQuadraticFourthMoment318
