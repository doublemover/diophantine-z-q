module
public import ConstructedPrimaryDepths318
public section
noncomputable section
namespace SelectedTraceFromDepths318
open CircuitReplay ConcretePadic318
open ContactPrimeForms318 ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ScaledContactWeights318 ScaledDetectorChain318 DetectorWeightPreparation318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- The eight remaining norm/comparison bounds are tied to the SAME actual
embedding and original half-point orders. This is the precise outstanding
local logarithm/Padé join, not a free sixteen-leaf success hypothesis. -/
@[expose] def Inputs (q : ℚ) (h u w : ℤ) (hp : Values C u w) (Mminus Mplus : ℕ) : Prop :=
  ∀ j : Fin 3, ∀ i : Fin 5,
    let p := (row C u w j i).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
    ∃ (rho : ℚ_[p]) (hr : rho^2=2),
      SelectedQuotientOrders318.order p rho hr∣Mminus ∧
      SelectedQuotientOrders318.order p (-rho) (negative_root p rho hr)∣Mplus ∧
      ConstructedPrimaryDepths318.Remaining (place p rho hr) (DetectorGateWitness318.witness q labels h)

/-- All selected trace hypotheses are now produced from original fixed
avoidance, actual quotient orders, the exact CRT and only eight remaining
norm/comparison estimates. Both denominator units, all opposite parity and
eight primary leaf estimates are proved, not retained as caller inputs. -/
theorem selected_trace (hn : ∀ j, labels j≠0) (q : ℚ) (h : ℕ) (u w : ℤ)
    (hp : Values C u w) (ha : SelectedOppositeGood318.Avoidance C u w hp)
    (Mminus Mplus : ℕ) (hi : Inputs C q (h:ℤ) u w hp Mminus Mplus)
    (hprimary : Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*Mminus) h 0)
    (hopposite : Nat.ModEq Mplus h 1)
    (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0) :
    SelectedContactDenominators318.SelectedTrace C q (h:ℤ) u w hp := by
  intro j i
  dsimp only
  let p := (row C u w j i).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
  obtain ⟨hlarge,hcunit,hdunit⟩ := ha j i
  obtain ⟨rho,hr,hm,hp',hremaining⟩ := hi j i
  obtain ⟨hdel,hopp⟩ := SelectedOppositeGood318.actual_opposite C hn q (h:ℤ) u w hp ha
    hzero hone hg j i
  have hc : ThreeDetectorArithmetic318.scales labels j≠0 := by
    rw [scales_eq]
    exact scaleRoot_ne labels hn j
  have hd := denominator_ne C w hp.nonzero
  have ht : ClearedContactForms318.parameter C u w=(u:ℚ)/(denominator C w)^2 := rfl
  have hdval : padicValRat p (denominator C w)=0 := by
    rw [rational_value p _ hd] at hdunit
    exact_mod_cast hdunit
  have hdelne : delta (ThreeDetectorArithmetic318.scales labels j)
      (ClearedContactForms318.parameter C u w)≠0 := by
    intro he
    rw [he,(rationalPlace p).map_zero] at hdel
    simpa using hdel
  have hdelval : padicValRat p (delta (ThreeDetectorArithmetic318.scales labels j)
      (ClearedContactForms318.parameter C u w))=0 := by
    have he := hdel
    rw [rational_value p _ hdelne] at he
    exact_mod_cast he
  have hweights := SelectedContactWeightValues318.weight_values p _ _ _ hc hd hcunit hdunit
    (by simpa only [ht] using hdel) (row C u w j) (linear_eq C u w j)
    (SelectedProductDepth318.actual_product C hn u w hp j i)
  have hcharts := SelectedActualChartLeaves318.depths p (by omega) rho hr
    (MergedContactPrimePattern318.product C u w) Mminus Mplus h (selected_divides C u w (j,i))
    (SelectedQuotientOrders318.entry_of_order_dvd p rho hr Mminus hm)
    (SelectedQuotientOrders318.entry_of_order_dvd p (-rho) _ Mplus hp')
    hprimary hopposite q labels
  have hprim := ConstructedPrimaryDepths318.all_positive p rho hr _
    (DetectorGateWitness318.witness_first107 0 q labels (h:ℤ) hzero hone hg)
    (ThreeDetectorArithmetic318.scales labels j) ((u:ℚ)/(denominator C w)^2)
    hweights (fun k => (hcharts k).1) (fun k => (hcharts k).2) hremaining
  refine ⟨by omega,hdval,hdelval,rho,hr,?_,hopp rho hr⟩
  simpa only [ht] using hprim

/-- Literal stored190/241/292 square denominators with no supplied
opposite-leaf or whole-source constraints. The eight remaining comparison
bounds and actual Gaussian-order divisibility are still explicit. -/
theorem square_denominators (hn : ∀ j, labels j≠0) (q : ℚ) (h : ℕ) (u w : ℤ)
    (hp : Values C u w) (ha : SelectedOppositeGood318.Avoidance C u w hp)
    (Mminus Mplus : ℕ) (hi : Inputs C q (h:ℤ) u w hp Mminus Mplus)
    (hprimary : Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*Mminus) h 0)
    (hopposite : Nat.ModEq Mplus h 1)
    (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0)
    (hb : ∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness q labels (h:ℤ)
      (ClearedContactForms318.parameter C u w) (190+51*j.val)) :
    ∀ j : Fin 3, IsSquare (ThreeDetectorUniformFamily318.witness q labels (h:ℤ)
      (ClearedContactForms318.parameter C u w) (190+51*j.val)).den :=
  SelectedContactDenominators318.square_denominators C hn q (h:ℤ) u w hp hb
    (selected_trace C hn q h u w hp ha Mminus Mplus hi hprimary hopposite hzero hone hg)

end SelectedTraceFromDepths318
