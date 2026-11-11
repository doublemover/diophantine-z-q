module
public import ConstructedLeafParity318
public section
noncomputable section
namespace SelectedCurveUnits318
open ConcreteG8Domain ConcretePadic318 ValuativeOrbitBounds318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]

lemma place_conjugate (rho : ℚ_[p]) (hr : rho^2=2) (a b : ℚ) :
    place p rho hr (pair a (-b))=place p (-rho) (negative_root p rho hr) (pair a b) := by
  change Padic.addValuation (embedding p rho hr (pair a (-b)))=
    Padic.addValuation (embedding p (-rho) (negative_root p rho hr) (pair a b))
  rw [conjugate_embedding]

/-- The conjugated coefficient is a unit away from the actual norm49.
Both integral bounds come from the original two embeddings. -/
theorem conjugate_unit (rho : ℚ_[p]) (hr : rho^2=2) (h7 : ¬p∣49) :
    place p rho hr (pair 11 6)=0 := by
  have hD : D=pair 11 (-6) := by ext <;> norm_num [D,i,pair,pow_two]
  have hm := ActualSplitOrbitEntry318.coefficient_bound p rho hr
  have hp := ActualSplitOrbitEntry318.coefficient_bound p (-rho) (negative_root p rho hr)
  rw [Bound,hD] at hm hp
  have hc : place p rho hr (pair 11 6)=
      place p (-rho) (negative_root p rho hr) (pair 11 (-6)) := by
    simpa only [neg_neg] using place_conjugate p rho hr 11 (-6)
  have he := norm_valuation p rho hr 11 (-6)
  have hn : (11^2-2*(-6)^2:ℚ)=49 := by norm_num
  rw [hn,rational_nat_unit p 49 h7] at he
  rw [hc]
  apply le_antisymm
  · calc
      place p (-rho) (negative_root p rho hr) (pair 11 (-6)) ≤
          place p rho hr (pair 11 (-6))+
          place p (-rho) (negative_root p rho hr) (pair 11 (-6)) := le_add_of_nonneg_left hm
      _ = 0 := he
  · exact hp

/-- Actual opposite leaf parity is produced from the original prefix and
fixed excluded norm primes. It is not a new source-system assumption. -/
theorem actual_even (hp : 3≤p) (h7 : ¬p∣49) (rho : ℚ_[p]) (hr : rho^2=2)
    (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (hzero : h≠0) (hone : h≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0)
    (c t : ℚ) :
    ∀ a∈ActualDetectorFold318.leaves
      (ScaledDetectorChain318.view (DetectorGateWitness318.witness q labels h) c t),
      ValuationEvenNormChain.EvenAt (place p (-rho) (negative_root p rho hr)) a.2 :=
  ConstructedLeafParity318.actual_even q labels h hzero hone hg _
    (conjugate_unit p (-rho) _ h7) (SelectedPositiveDelta318.two_unit p hp (-rho) _) c t

end SelectedCurveUnits318
