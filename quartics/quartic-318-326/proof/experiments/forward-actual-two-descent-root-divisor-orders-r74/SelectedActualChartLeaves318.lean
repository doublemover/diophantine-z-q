module
public import SelectedOppositeGood318
public section
noncomputable section
namespace SelectedActualChartLeaves318
open ConcreteG8Domain ConcretePadic318 ValuativeOrbitBounds318
open CoherentMultipleCharts318 (chartU chartV)
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

lemma actual_u (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (j : Fin 8) :
    PadeRatioWitness318.u (DetectorGateWitness318.witness q labels h) j=
      CoherentMultiplePrefix318.u labels h j := by
  calc
    _ = PadeRatioWitness318.u (ActualPadeRatios318.base q labels h) j := by
      fin_cases j <;> rfl
    _ = _ := ActualPadeRatios318.base_u q labels h j

lemma actual_v (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (j : Fin 8) :
    PadeRatioWitness318.v (DetectorGateWitness318.witness q labels h) j=
      CoherentMultiplePrefix318.v labels h j := by
  calc
    _ = PadeRatioWitness318.v (ActualPadeRatios318.base q labels h) j := by
      fin_cases j <;> rfl
    _ = _ := ActualPadeRatios318.base_v q labels h j

@[expose] def linearLeaf (w : CircuitReplay.Assignment) (j : Fin 4) : K :=
  let v := PadeRatioWitness318.v w (j.natAdd 4)
  pair (v.re-1) (-v.im)

lemma conjugated_delta (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2) (z : K) :
    place p rho hr (pair (z.re-1) (-z.im))=
      place p (-rho) (negative_root p rho hr) (z-1) := by
  have he : z-1=pair (z.re-1) z.im := by ext <;> simp [pair]
  rw [he,SelectedCurveUnits318.place_conjugate]

/-- The eight simple leaves really use the first and second halves of the
original coherent charts, including the conjugation of the UNSQUARED delta. -/
theorem depths (p : ℕ) [Fact p.Prime] (hp : 3≤p)
    (rho : ℚ_[p]) (hr : rho^2=2) (Pi Mminus Mplus h : ℕ)
    (hpPi : p∣Pi)
    (hm : SelectedFormalEntry318.Entry p rho hr Mminus)
    (hp' : SelectedFormalEntry318.Entry p (-rho) (negative_root p rho hr) Mplus)
    (hprimary : Nat.ModEq (Pi^3*Mminus) h 0) (hopposite : Nat.ModEq Mplus h 1)
    (q : ℚ) (labels : Fin 4 → ℤ) :
    ∀ j : Fin 4,
      Bound (place p rho hr) 4
        (PadeRatioWitness318.u (DetectorGateWitness318.witness q labels (h:ℤ)) (j.castAdd 4)) ∧
      Bound (place p rho hr) 4
        (linearLeaf (DetectorGateWitness318.witness q labels (h:ℤ)) j) := by
  intro j
  have he := SelectedPositiveDelta318.original_charts p hp rho hr Pi Mminus Mplus h
    hpPi hm hp' hprimary hopposite (labels j)
  constructor
  · rw [actual_u]
    simpa only [CoherentMultiplePrefix318.u,CoherentMultiplePrefix318.parameters,Fin.append_left] using he.1
  · unfold linearLeaf Bound
    rw [conjugated_delta,actual_v]
    simpa only [CoherentMultiplePrefix318.v,CoherentMultiplePrefix318.parameters,Fin.append_right] using he.2.2.2

end SelectedActualChartLeaves318
