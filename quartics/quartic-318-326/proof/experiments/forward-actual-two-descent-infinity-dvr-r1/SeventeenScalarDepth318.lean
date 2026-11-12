module
public import AllSmallPrimeProgression318
public section
noncomputable section
namespace SeventeenScalarDepth318
open ConcreteG8Domain (K)
open CoherentMultipleCharts318 (chartU)
open GeneratorScalarProgression318 (normCoefficient)
open ValuativeOrbitBounds318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

lemma coefficients (e : ℕ) (m : ℤ) :
    Bound (ConcretePadic318.rationalPlace 17) ((e:ℤ)+1) (chartU (20*17^e*m)).re ∧
    Bound (ConcretePadic318.rationalPlace 17) ((e:ℤ)+1) (chartU (20*17^e*m)).im := by
  obtain ⟨ρ,hρ⟩ := ActualSeventeenEntry318.square_root_two
  exact SeventeenOrbitPrecision318.recover_coefficients ρ hρ _ _
    (SeventeenOrbitPrecision318.place_precision ρ hρ e m).1
    (SeventeenOrbitPrecision318.place_precision (-ρ)
      (ConcretePadic318.negative_root 17 ρ hρ) e m).1

lemma norm_ne (h : ℤ) (hh : h≠0) : normCoefficient (chartU h)≠0 := by
  rw [ScalarTranslatedIndex318.norm_coefficient]
  exact AnchorNorm318.norm_ne_zero (fun he => hh ((CoherentMultipleCharts318.chartU_zero_iff h).mp he))

lemma half_trace_ne (h : ℤ) (hh : h≠0) : ((chartU h)^2).re≠0 :=
  ScalarPackedLocalUnit318.half_trace_ne _ (norm_ne h hh)

lemma rational_depth (r : ℤ) (x : ℚ) (hx : x≠0)
    (h : Bound (ConcretePadic318.rationalPlace 17) r x) : r≤padicValRat 17 x := by
  rw [Bound,ConcretePadic318.rational_value 17 x hx] at h
  exact_mod_cast h

/-- Both scalar common-index leaves grow on the actual17 progression.
The split norm may have extra cancellation, so only justified lower bounds
are asserted. Its finite value is retained when choosing the later label. -/
theorem actual_depths (e : ℕ) (m : ℤ) (hm : m≠0) :
    2*((e:ℤ)+1)≤padicValRat 17 (normCoefficient (chartU (20*17^e*m))) ∧
    2*((e:ℤ)+1)≤padicValRat 17 ((chartU (20*17^e*m))^2).re := by
  have hn : (20:ℤ)*17^e*m≠0 := mul_ne_zero (by positivity) hm
  obtain ⟨ha,hb⟩ := coefficients e m
  let v := ConcretePadic318.rationalPlace 17
  have hterm := bmul_unit_left v (bnat v 2) (bsquare v hb)
  constructor
  · apply rational_depth _ _ (norm_ne _ hn)
    change Bound v (2*((e:ℤ)+1)) _
    simpa only [normCoefficient] using bsub v (bsquare v ha) hterm
  · apply rational_depth _ _ (half_trace_ne _ hn)
    rw [ScalarHalfTraceDepth318.half_trace]
    exact badd v (bsquare v ha) hterm

/-- The fixed scalar label retains its original6-power and arbitrary
anchor3-power. An extra20·17^e factor gives an actual norm-depth lower bound,
not an assumed local realization of the translated scalar point. -/
theorem label_depth (A B N e d : ℕ) (hd : d≠0) :
    let n := ScalarPreparedResidues318.scalarLabel A B
      (PreparedAnchorLabels318.multiplier N (20*17^e*d))
    2*((e:ℤ)+1)≤padicValRat 17 (ActualScalarRoot318.inverseNorm n) := by
  dsimp only
  have hd' : 20*17^e*d≠0 := mul_ne_zero (by positivity) hd
  have hd'' := PreparedAnchorLabels318.multiplier_ne N _ hd'
  have hn := (ScalarPreparedResidues318.label_domains A B _ hd'').1
  rw [ScalarTranslatedIndex318.scalar_inverse_norm _ (by omega)]
  have hi : ScalarPreparedResidues318.scalarLabel A B
      (PreparedAnchorLabels318.multiplier N (20*17^e*d))-1=
      20*(17:ℤ)^e*((6:ℤ)^(A+B+15)*3^N*(d:ℤ)) := by
    unfold ScalarPreparedResidues318.scalarLabel PreparedAnchorLabels318.multiplier
    push_cast
    ring
  rw [hi]
  exact (actual_depths e _ (mul_ne_zero (by positivity) (by exact_mod_cast hd))).1

end SeventeenScalarDepth318
