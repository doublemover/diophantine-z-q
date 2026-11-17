module
public import SelectedIntegralTranslation318
public section
noncomputable section
namespace SelectedNormTestValues318
open ConcreteG8Domain ConcretePadic318 ValuativeOrbitBounds318
open CoherentMultipleCharts318 (chartU chartV)
open GeneratorScalarProgression318 (normCoefficient)
open RawDetector318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

lemma norm_bound (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (x : K) (a b : ℤ) (ha : Bound (place p rho hr) a x)
    (hb : Bound (place p (-rho) (negative_root p rho hr)) b x) :
    Bound (rationalPlace p) (a+b) (normCoefficient x) := by
  have he := norm_valuation p rho hr x.re x.im
  have hx : pair x.re x.im=x := by cases x; rfl
  rw [hx] at he
  change ((a+b:ℤ):WithTop ℤ)≤rationalPlace p (x.re^2-2*x.im^2)
  rw [←he]
  exact_mod_cast add_le_add ha hb

lemma test0_actual (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    test0 0 (DetectorGateWitness318.witness q labels h)=pair (normCoefficient (chartU h)) 0 := by
  have he : DetectorGateWitness318.witness q labels h 37=normCoefficient (chartU h) := rfl
  simp only [test0,one_mul,he]

/-- The norm test uses the square of the actual translated chart, with the
original compression orientation. No separate square root is supplied. -/
lemma test5_actual (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (hh : h≠0) :
    test5 0 (DetectorGateWitness318.witness q labels h)=
      pair ((normCoefficient (chartU (h-1)))^2) 0 := by
  let w := DetectorGateWitness318.witness q labels h
  let base := ActualPadeRatios318.base q labels h
  have h76 : w 76=(CompressedOrientation318.fV base).re := rfl
  have h77 : w 77=(CompressedOrientation318.fV base).im := rfl
  have hf : CompressedOrientation318.fV base=(chartU (h-1))^2 := by
    rw [ActualPadeRatios318.base_fV,ScalarTranslatedIndex318.shifted_chart h hh]
    ring
  have ht : test5 0 w=pair (normCoefficient (CompressedOrientation318.fV base)) 0 := by
    ext <;> simp only [test5,one_mul,h76,h77,normCoefficient,pair]
    all_goals ring
  change test5 0 w=_
  rw [ht,hf,ScalarTranslatedIndex318.norm_coefficient,AnchorNorm318.norm_pow,
    ←ScalarTranslatedIndex318.norm_coefficient]

/-- Both actual rational norm tests are produced from the SAME primary
and opposite charts: depths4 for nH and2 for N(fV0). -/
theorem norm_tests (p : ℕ) [Fact p.Prime] (hp : 76176<p)
    (rho : ℚ_[p]) (hr : rho^2=2) (h : ℤ) (hzero : h≠0)
    (hm : Near (place p rho hr) 4 (chartU h) (chartV h))
    (hp' : Near (place p (-rho) (negative_root p rho hr)) 1 (chartU (h-1)) (chartV (h-1)))
    (q : ℚ) (labels : Fin 4 → ℤ) :
    Bound (place p rho hr) 4 (test0 0 (DetectorGateWitness318.witness q labels h)) ∧
    Bound (place p rho hr) 2 (test5 0 (DetectorGateWitness318.witness q labels h)) := by
  obtain ⟨hshift,hbase⟩ := SelectedIntegralTranslation318.opposite_factors p hp rho hr h hm hp'
  have hnH := norm_bound p rho hr (chartU h) 4 0 hm.1 hbase
  have hnV := norm_bound p rho hr (chartU (h-1)) 0 1 hshift hp'.1
  constructor
  · rw [test0_actual,Bound,place_rational]
    simpa only [add_zero] using hnH
  · rw [test5_actual q labels h hzero,Bound,place_rational]
    simpa only [zero_add,mul_one] using bsquare (rationalPlace p) hnV

end SelectedNormTestValues318
