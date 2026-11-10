module
public import IntegralPolynomialPrecision318
public section
noncomputable section
namespace ActualSixComparisonValues318
open CircuitReplay ConcreteG8Domain RawDetector318 PadeRatioWitness318
open ActualPadeRatios318 ValuativeOrbitBounds318 ConcretePadic318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

lemma filled_comparisons (w : Assignment) (z : Data) :
    test10 0 (DetectorGateWitness318.fill (fill w z))=z.primaryRatio 0-SourceContact318.conj (z.alternateRatio 0) ∧
    test11 0 (DetectorGateWitness318.fill (fill w z))=z.primaryRatio 1-SourceContact318.conj (z.alternateRatio 1) ∧
    test12 0 (DetectorGateWitness318.fill (fill w z))=z.primaryRatio 2-SourceContact318.conj (z.alternateRatio 2) ∧
    test13 0 (DetectorGateWitness318.fill (fill w z))=z.primaryRatio 3-SourceContact318.conj (z.alternateRatio 3) := by
  repeat' constructor <;> ext <;>
    simp [test10,test11,test12,test13,DetectorGateWitness318.fill,fill,SourceContact318.conj,pair]

lemma filled_beta (w : Assignment) (z : Data) :
    test14 0 (DetectorGateWitness318.fill (fill w z))=
      z.primaryRatio 0-3723*(2*(w 0:K)+1)^2 := by
  ext <;> simp [test14,DetectorGateWitness318.fill,DetectorGateWitness318.value118,fill,pair,pow_two] <;> ring

lemma filled_lucas (w : Assignment) (z : Data) :
    test15 0 (DetectorGateWitness318.fill (fill w z))=
      IntegralPolynomialPrecision318.lucas (z.primaryRatio 1) (z.primaryRatio 2) (z.primaryRatio 3)-1 := by
  ext <;> simp [test15,DetectorGateWitness318.fill,DetectorGateWitness318.value119,
    DetectorGateWitness318.value120,DetectorGateWitness318.value121,DetectorGateWitness318.value122,
    DetectorGateWitness318.value123,DetectorGateWitness318.value124,fill,
    IntegralPolynomialPrecision318.lucas,pair,pow_two] <;> ring

lemma conjugate_bound (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (r : ℤ) (x : K) (n : ℤ)
    (he : Bound (place p (-rho) (negative_root p rho hr)) r (x-(n:K))) :
    Bound (place p rho hr) r (SourceContact318.conj x-(n:K)) := by
  have hc : SourceContact318.conj x-(n:K)=SourceContact318.conj (x-(n:K)) := by
    rw [map_sub,map_intCast]
  rw [hc]
  change (r:WithTop ℤ)≤place p rho hr (pair ((x-(n:K)).re) (-((x-(n:K)).im)))
  rw [SelectedCurveUnits318.place_conjugate]
  exact he

/-- All six literal raw detector comparisons are now consequences of actual
ratio errors and the original integer beta/Lucas equations. -/
theorem comparisons (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (a : ℤ) (labels : Fin 4 → ℤ) (h : ℤ)
    (hbeta : labels 0=3723*(2*a+1)^2)
    (hlucas : (labels 2)^2-labels 1*(labels 1-2)*labels 2*labels 3+
      (labels 1-2)^2*(labels 3)^2=1)
    (hprimary : ∀ j, Bound (place p rho hr) 16
      ((construct (base (a:ℚ) labels h)).primaryRatio j-(labels j:K)))
    (halt : ∀ j, Bound (place p (-rho) (negative_root p rho hr)) (if j=0 then 8 else 16)
      ((construct (base (a:ℚ) labels h)).alternateRatio j-(labels j:K))) :
    SelectedSixComparisonTrace318.Comparisons (place p rho hr)
      (DetectorGateWitness318.witness (a:ℚ) labels h) := by
  let z := construct (base (a:ℚ) labels h)
  let v := place p rho hr
  have hcomp (j : Fin 4) : Bound v (if j=0 then 8 else 16)
      (z.primaryRatio j-SourceContact318.conj (z.alternateRatio j)) := by
    have hp := weaken v (hprimary j) (by split_ifs <;> norm_num : (if j=0 then 8 else 16:ℤ)≤16)
    have ha := conjugate_bound p rho hr _ (z.alternateRatio j) (labels j) (halt j)
    convert bsub v hp ha using 1 <;> ring
  obtain ⟨e0,e1,e2,e3⟩ := filled_comparisons (base (a:ℚ) labels h) z
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [show test10 0 (DetectorGateWitness318.witness (a:ℚ) labels h)=
        z.primaryRatio 0-SourceContact318.conj (z.alternateRatio 0) from e0]
    exact weaken v (hcomp 0) (by norm_num)
  · rw [show test11 0 (DetectorGateWitness318.witness (a:ℚ) labels h)=
        z.primaryRatio 1-SourceContact318.conj (z.alternateRatio 1) from e1]
    exact weaken v (hcomp 1) (by norm_num)
  · rw [show test12 0 (DetectorGateWitness318.witness (a:ℚ) labels h)=
        z.primaryRatio 2-SourceContact318.conj (z.alternateRatio 2) from e2]
    exact weaken v (hcomp 2) (by norm_num)
  · rw [show test13 0 (DetectorGateWitness318.witness (a:ℚ) labels h)=
        z.primaryRatio 3-SourceContact318.conj (z.alternateRatio 3) from e3]
    exact weaken v (hcomp 3) (by norm_num)
  · have he := filled_beta (base (a:ℚ) labels h) z
    have hb : (base (a:ℚ) labels h) 0=(a:ℚ) :=
      CoherentMultiplePrefix318.witness_input (a:ℚ) labels h
    rw [hb] at he
    have hcast : (labels 0:K)=3723*(2*((a:ℚ):K)+1)^2 := by
      rw [hbeta]
      push_cast <;> rfl
    change Bound v 4 (test14 0 (DetectorGateWitness318.fill (fill (base (a:ℚ) labels h) z)))
    rw [he,←hcast]
    exact weaken v (hprimary 0) (by norm_num)
  · change Bound v 13 (test15 0 (DetectorGateWitness318.fill (fill (base (a:ℚ) labels h) z)))
    rw [filled_lucas]
    exact weaken v (IntegralPolynomialPrecision318.lucas_error v (by norm_num : (0:ℤ)≤16)
      (z.primaryRatio 1) (z.primaryRatio 2) (z.primaryRatio 3) (labels 1) (labels 2) (labels 3)
      (hprimary 1) (hprimary 2) (hprimary 3) hlucas) (by norm_num)

end ActualSixComparisonValues318
