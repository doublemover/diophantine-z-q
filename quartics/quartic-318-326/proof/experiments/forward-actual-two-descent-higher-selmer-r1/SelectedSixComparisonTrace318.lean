module
public import SelectedNormTestValues318
public section
noncomputable section
namespace SelectedSixComparisonTrace318
open ConcreteG8Domain ConcretePadic318 ValuativeOrbitBounds318 RawDetector318
open ContactPrimeForms318 ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- Only the four actual primary-versus-conjugate-alternate ratios and the
actual beta/Lucas residuals remain. Both rational norm tests are produced. -/
@[expose] def Comparisons (v : AddValuation K (WithTop ℤ)) (w : CircuitReplay.Assignment) : Prop :=
  Bound v 4 (test10 0 w) ∧ Bound v 13 (test11 0 w) ∧
  Bound v 13 (test12 0 w) ∧ Bound v 13 (test13 0 w) ∧
  Bound v 4 (test14 0 w) ∧ Bound v 13 (test15 0 w)

@[expose] def Inputs (q : ℚ) (h u w : ℤ) (hp : Values C u w) (Mminus Mplus : ℕ) : Prop :=
  ∀ j : Fin 3, ∀ i : Fin 5,
    let p := (row C u w j i).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
    ∃ (rho : ℚ_[p]) (hr : rho^2=2),
      SelectedQuotientOrders318.order p rho hr∣Mminus ∧
      SelectedQuotientOrders318.order p (-rho) (negative_root p rho hr)∣Mplus ∧
      Comparisons (place p rho hr) (DetectorGateWitness318.witness q labels h)

/-- The two actual norm bounds fill the missing entries of the previous
same-root eight-test interface, without enlarging either CRT modulus. -/
theorem with_norms (q : ℚ) (h : ℕ) (u w : ℤ) (hp : Values C u w)
    (ha : SelectedOppositeGood318.Avoidance C u w hp)
    (Mminus Mplus : ℕ) (hi : Inputs C q (h:ℤ) u w hp Mminus Mplus)
    (hprimary : Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*Mminus) h 0)
    (hopposite : Nat.ModEq Mplus h 1) (hzero : (h:ℤ)≠0) :
    SelectedTraceFromDepths318.Inputs C q (h:ℤ) u w hp Mminus Mplus := by
  intro j i
  dsimp only
  let p := (row C u w j i).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
  obtain ⟨rho,hr,hm,hp',hcomp⟩ := hi j i
  have hlarge := (ha j i).1
  have heM := SelectedQuotientOrders318.entry_of_order_dvd p rho hr Mminus hm
  have heP := SelectedQuotientOrders318.entry_of_order_dvd p (-rho) _ Mplus hp'
  have hnearM := SelectedFormalEntry318.primary p rho hr
    (MergedContactPrimePattern318.product C u w) Mminus h (selected_divides C u w (j,i))
    heM hprimary 1
  have hnearP := SelectedFormalEntry318.opposite p (-rho) (negative_root p rho hr)
    Mplus h heP hopposite 1
  simp only [one_mul] at hnearM hnearP
  have hn := SelectedNormTestValues318.norm_tests p hlarge rho hr (h:ℤ) hzero hnearM hnearP q labels
  exact ⟨rho,hr,hm,hp',hn.1,hn.2,hcomp⟩

/-- Literal selected trace success now needs only the six actual logarithm,
Padé, beta and Lucas comparison estimates, at the same selected roots/h. -/
theorem selected_trace (hn : ∀ j, labels j≠0) (q : ℚ) (h : ℕ) (u w : ℤ)
    (hp : Values C u w) (ha : SelectedOppositeGood318.Avoidance C u w hp)
    (Mminus Mplus : ℕ) (hi : Inputs C q (h:ℤ) u w hp Mminus Mplus)
    (hprimary : Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*Mminus) h 0)
    (hopposite : Nat.ModEq Mplus h 1)
    (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0) :
    SelectedContactDenominators318.SelectedTrace C q (h:ℤ) u w hp :=
  SelectedTraceFromDepths318.selected_trace C hn q h u w hp ha Mminus Mplus
    (with_norms C q h u w hp ha Mminus Mplus hi hprimary hopposite hzero)
    hprimary hopposite hzero hone hg

/-- Exact original pole denominator conclusion, with the two previously
supplied norm estimates removed from the required inputs. -/
theorem square_denominators (hn : ∀ j, labels j≠0) (q : ℚ) (h : ℕ) (u w : ℤ)
    (hp : Values C u w) (ha : SelectedOppositeGood318.Avoidance C u w hp)
    (Mminus Mplus : ℕ) (hi : Inputs C q (h:ℤ) u w hp Mminus Mplus)
    (hprimary : Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*Mminus) h 0)
    (hopposite : Nat.ModEq Mplus h 1)
    (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0)
    (hb : ∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness q labels (h:ℤ)
      (parameter C u w) (190+51*j.val)) :
    ∀ j : Fin 3, IsSquare (ThreeDetectorUniformFamily318.witness q labels (h:ℤ)
      (parameter C u w) (190+51*j.val)).den :=
  SelectedContactDenominators318.square_denominators C hn q (h:ℤ) u w hp hb
    (selected_trace C hn q h u w hp ha Mminus Mplus hi hprimary hopposite hzero hone hg)

end SelectedSixComparisonTrace318
