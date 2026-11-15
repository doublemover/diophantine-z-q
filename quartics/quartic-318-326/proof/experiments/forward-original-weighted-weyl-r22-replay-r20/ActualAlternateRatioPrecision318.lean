module
public import ActualMixedLogPrecision318
public section
noncomputable section
namespace ActualAlternateRatioPrecision318
open ConcreteG8Domain (K)
open CoherentMultipleCharts318 (chartU chartV)
open ActualPadeRatios318 PadeRatioWitness318 Pade21Domains
open ValuativeOrbitBounds318 ConcretePadic318 ActualSourceRatioParameters318
set_option maxHeartbeats 1000000

/-- The original branch choice is linear J for beta and full J-Padé for the
other three labels, all divided by the SAME original G-Padé common log. -/
lemma alternate (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (hzero : h≠0) (j : Fin 4) :
    (construct (base q labels h)).alternateRatio j=
      (-chartU (labels j*(h-1))*(if j=0 then 1-(chartV (labels j*(h-1))-1)/5
        else PJ (chartV (labels j*(h-1))-1)/QJ (chartV (labels j*(h-1))-1)))/
      ((-chartU (h-1)/chartV (h-1))*(PG (ConcreteG8Domain.D*(chartU (h-1))^4)/
        QG (ConcreteG8Domain.D*(chartU (h-1))^4))) := by
  dsimp only [construct]
  rw [common_parameter q labels h hzero,CoherentMultipleCharts318.D_eq]
  rw [base_u]
  simp only [CoherentMultiplePrefix318.u,CoherentMultiplePrefix318.parameters,Fin.append_right]
  unfold alternatePolynomial
  split_ifs with hj
  · subst j
    simp only [base_v,CoherentMultiplePrefix318.v,CoherentMultiplePrefix318.parameters,Fin.append_right]
  · rw [base_v]
    rfl

theorem alternate_precision (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (rho : ℚ_[p]) (hr : rho^2=2) (h7 : ¬p∣49)
    (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (hzero : h≠0) (hone : h≠1)
    (hn : ∀ j, labels j≠0)
    (hbase : Near (place p rho hr) 1 (chartU (h-1)) (chartV (h-1)))
    (hall : ∀ j, Near (place p rho hr) 1 (chartU (labels j*(h-1))) (chartV (labels j*(h-1)))) :
    ∀ j, Bound (place p rho hr) (if j=0 then 8 else 16)
      ((construct (base q labels h)).alternateRatio j-(labels j:K)) := by
  intro j
  rw [alternate q labels h hzero j]
  obtain ⟨h8,h16⟩ := ActualMixedLogPrecision318.original_ratios p hp rho hr h7
    (h-1) (labels j) (sub_ne_zero.mpr hone) (hn j) hbase (hall j)
  split_ifs with hj
  · exact h8
  · exact h16

/-- Original selected-prime CRT and half-point orders now produce ALL EIGHT
actual approximation estimates, with no ratio-precision assumption. -/
theorem selected (p : ℕ) [Fact p.Prime] (hp : 19≤p) (rho : ℚ_[p]) (hr : rho^2=2)
    (h7 : ¬p∣49) (Pi Mminus Mplus h : ℕ) (hpPi : p∣Pi)
    (hm : SelectedQuotientOrders318.order p rho hr∣Mminus)
    (hp' : SelectedQuotientOrders318.order p (-rho) (negative_root p rho hr)∣Mplus)
    (hprimary : Nat.ModEq (Pi^3*Mminus) h 0) (hopposite : Nat.ModEq Mplus h 1)
    (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1) :
    (∀ j, Bound (place p rho hr) 16
      ((construct (base q labels (h:ℤ))).primaryRatio j-(labels j:K))) ∧
    (∀ j, Bound (place p (-rho) (negative_root p rho hr)) (if j=0 then 8 else 16)
      ((construct (base q labels (h:ℤ))).alternateRatio j-(labels j:K))) := by
  have hnearM := SelectedFormalEntry318.primary p rho hr Pi Mminus h hpPi
    (SelectedQuotientOrders318.entry_of_order_dvd p rho hr Mminus hm) hprimary
  have hnearP := SelectedFormalEntry318.opposite p (-rho) (negative_root p rho hr) Mplus h
    (SelectedQuotientOrders318.entry_of_order_dvd p (-rho) _ Mplus hp') hopposite
  constructor
  · exact primary_precision p hp rho hr h7 q labels (h:ℤ) hzero hn
      (by simpa only [one_mul] using hnearM 1) (fun j => hnearM (labels j))
  · exact alternate_precision p hp (-rho) (negative_root p rho hr) h7 q labels (h:ℤ)
      hzero hone hn (by simpa only [one_mul] using hnearP 1) (fun j => hnearP (labels j))

end ActualAlternateRatioPrecision318
