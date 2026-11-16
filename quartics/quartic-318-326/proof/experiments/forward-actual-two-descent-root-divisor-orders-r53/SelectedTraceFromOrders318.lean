module
public import ActualSixComparisonValues318
public section
noncomputable section
namespace SelectedTraceFromOrders318
open ConcreteG8Domain ConcretePadic318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- Only actual residue-group orders remain at the fifteen selected prime
positions. There are NO supplied leaf valuations or ratio/comparison bounds. -/
@[expose] def Orders (u w : ℤ) (hp : Values C u w) (Mminus Mplus : ℕ) : Prop :=
  ∀ j : Fin 3, ∀ i : Fin 5,
    let p := (row C u w j i).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
    ∃ (rho : ℚ_[p]) (hr : rho^2=2),
      SelectedQuotientOrders318.order p rho hr∣Mminus ∧
      SelectedQuotientOrders318.order p (-rho) (negative_root p rho hr)∣Mplus

theorem comparison_inputs (a : ℤ) (hn : ∀ j, labels j≠0)
    (hbeta : labels 0=3723*(2*a+1)^2)
    (hlucas : (labels 2)^2-labels 1*(labels 1-2)*labels 2*labels 3+
      (labels 1-2)^2*(labels 3)^2=1)
    (h : ℕ) (u w : ℤ) (hp : Values C u w)
    (ha : SelectedOppositeGood318.Avoidance C u w hp)
    (Mminus Mplus : ℕ) (hi : Orders C u w hp Mminus Mplus)
    (hprimary : Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*Mminus) h 0)
    (hopposite : Nat.ModEq Mplus h 1) (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1) :
    SelectedSixComparisonTrace318.Inputs C (a:ℚ) (h:ℤ) u w hp Mminus Mplus := by
  intro j i
  dsimp only
  let p := (row C u w j i).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
  obtain ⟨rho,hr,hm,hp'⟩ := hi j i
  have hlarge := (ha j i).1
  have h7 : ¬p∣49 := by
    intro hd
    have he := Nat.le_of_dvd (by norm_num : 0<49) hd
    omega
  obtain ⟨hP,hA⟩ := ActualAlternateRatioPrecision318.selected p (by omega) rho hr h7
    (MergedContactPrimePattern318.product C u w) Mminus Mplus h
    (selected_divides C u w (j,i)) hm hp' hprimary hopposite (a:ℚ) labels hn hzero hone
  exact ⟨rho,hr,hm,hp',ActualSixComparisonValues318.comparisons p rho hr a labels (h:ℤ)
    hbeta hlucas hP hA⟩

/-- The entire original selected-prime trace is produced from actual order
entry and fixed arithmetic labels. All sixteen leaves at all fifteen prime
positions are constructed on the same source assignment and same CRT h. -/
theorem selected_trace (a : ℤ) (hn : ∀ j, labels j≠0)
    (hbeta : labels 0=3723*(2*a+1)^2)
    (hlucas : (labels 2)^2-labels 1*(labels 1-2)*labels 2*labels 3+
      (labels 1-2)^2*(labels 3)^2=1)
    (h : ℕ) (u w : ℤ) (hp : Values C u w)
    (ha : SelectedOppositeGood318.Avoidance C u w hp)
    (Mminus Mplus : ℕ) (hi : Orders C u w hp Mminus Mplus)
    (hprimary : Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*Mminus) h 0)
    (hopposite : Nat.ModEq Mplus h 1) (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0) :
    SelectedContactDenominators318.SelectedTrace C (a:ℚ) (h:ℤ) u w hp :=
  SelectedSixComparisonTrace318.selected_trace C hn (a:ℚ) h u w hp ha Mminus Mplus
    (comparison_inputs C a hn hbeta hlucas h u w hp ha Mminus Mplus hi hprimary hopposite hzero hone)
    hprimary hopposite hzero hone hg

/-- Literal source slots190/241/292 now have square reduced denominators
without any selected-place detector, logarithm, or Padé-error premise. -/
theorem square_denominators (a : ℤ) (hn : ∀ j, labels j≠0)
    (hbeta : labels 0=3723*(2*a+1)^2)
    (hlucas : (labels 2)^2-labels 1*(labels 1-2)*labels 2*labels 3+
      (labels 1-2)^2*(labels 3)^2=1)
    (h : ℕ) (u w : ℤ) (hp : Values C u w)
    (ha : SelectedOppositeGood318.Avoidance C u w hp)
    (Mminus Mplus : ℕ) (hi : Orders C u w hp Mminus Mplus)
    (hprimary : Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*Mminus) h 0)
    (hopposite : Nat.ModEq Mplus h 1) (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0)
    (hb : ∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ)
      (parameter C u w) (190+51*j.val)) :
    ∀ j : Fin 3, IsSquare (ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ)
      (parameter C u w) (190+51*j.val)).den :=
  SelectedContactDenominators318.square_denominators C hn (a:ℚ) (h:ℤ) u w hp hb
    (selected_trace C a hn hbeta hlucas h u w hp ha Mminus Mplus hi hprimary hopposite hzero hone hg)

/-- The actual beta and Lucas labels, not an assumed polynomial solution,
supply the arithmetic relations consumed by the completed trace producer. -/
theorem fixed_labels (a : ℤ) (A B d : ℕ) (hd : d≠0)
    (h : ℕ) (u w : ℤ)
    (hp : Values (construct (FixedArithmeticLabels318.labels a A B d hd)) u w)
    (ha : SelectedOppositeGood318.Avoidance (construct (FixedArithmeticLabels318.labels a A B d hd)) u w hp)
    (Mminus Mplus : ℕ)
    (hi : Orders (construct (FixedArithmeticLabels318.labels a A B d hd)) u w hp Mminus Mplus)
    (hprimary : Nat.ModEq ((MergedContactPrimePattern318.product
      (construct (FixedArithmeticLabels318.labels a A B d hd)) u w)^3*Mminus) h 0)
    (hopposite : Nat.ModEq Mplus h 1) (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (FixedArithmeticLabels318.labels a A B d hd j)
      ((h:ℤ) • LocalGenerator318.P)≠0) :
    SelectedContactDenominators318.SelectedTrace
      (construct (FixedArithmeticLabels318.labels a A B d hd)) (a:ℚ) (h:ℤ) u w hp := by
  obtain ⟨hb,hl⟩ := FixedArithmeticLabels318.detector_relations a A B d hd
  exact selected_trace _ a (FixedArithmeticLabels318.labels_nonzero a A B d hd)
    hb hl h u w hp ha Mminus Mplus hi hprimary hopposite hzero hone hg

end SelectedTraceFromOrders318
