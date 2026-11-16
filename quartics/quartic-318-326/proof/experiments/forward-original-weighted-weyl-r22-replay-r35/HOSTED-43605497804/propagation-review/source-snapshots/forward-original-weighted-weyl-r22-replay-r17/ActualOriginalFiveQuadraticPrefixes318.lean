module
public import ActualOriginalSmoothIntegratedAbel318
public section
noncomputable section
namespace ActualOriginalFiveQuadraticPrefixes318
open QuadricCRTAssembly318 ActualOriginalJointPrefixControl318 ActualOriginalFiniteAbel318
open ActualOriginalQuadraticFourthMoment318 ActualOriginalFiniteFourierEnergy318
open ActualOriginalBoxOverlap318 ActualOriginalMinorQuadraticSupremum318
open ActualOriginalPrefixMinorMoment318 ActualOriginalRectangularMinorMoment318
open ActualOriginalShiftedQuadraticMoment318 ActualOriginalQuadraticEnergyCount318
open ActualOriginalFiveAxisCancellation318 ActualOriginalIntervalSliceIdentity318
open ActualOriginalUniformMixedPlaneVariation318 ActualOriginalMajorArcDomain318 MeasureTheory
open scoped BigOperators

@[expose] def quadraticTimeAxis (u : Coordinates ℤ) (c : ℤ) (H : ℕ) : TimeAxis (Coordinates ℤ) where
  step := u
  steps := 2*H
  phase := fun j t => fourier (c*(-(H : ℤ)+(j : ℤ))^2) (t : AddCircle (1 : ℝ))

@[expose] def quadraticFiveAxes (κ : ℤ) (H : ℕ) : List (TimeAxis (Coordinates ℤ)) :=
  [quadraticTimeAxis firstDirection 1 H,quadraticTimeAxis secondDirection 1 H,
    quadraticTimeAxis thirdDirection (-1) H,quadraticTimeAxis fourthDirection (-1) H,
    quadraticTimeAxis fifthDirection (-κ) H]

lemma actual_quadratic_prefix (u : Coordinates ℤ) (c : ℤ) (H n : ℕ) (t : ℝ) :
    prefix (fun j => (quadraticTimeAxis u c H).phase j t) n=
      quadraticSum (Finset.Icc (-(H : ℤ)) (-(H : ℤ)+(n : ℤ)-1)) c (t : AddCircle (1 : ℝ)) := by
  have hlen : ((-(H : ℤ)+(n : ℤ)-1)-(-(H : ℤ))+1).toNat=n := by omega
  simp only [quadraticSum,frequencySum,actual_integer_interval_sum,hlen,prefix,quadraticTimeAxis]

@[expose] def originalPrefixIntegralBudget (κ : ℤ) (H N : ℕ) (B δ : ℝ) : ℝ :=
  Real.sqrt (minorQuadraticBudget (-κ) H N ⌈B^2/(N : ℝ)⌉₊)*momentBudget H δ

lemma actual_prefix_integral_budget_nonneg (κ : ℤ) (H N : ℕ) (B δ : ℝ) (hδ : 0<δ) :
    0≤originalPrefixIntegralBudget κ H N B δ :=
  mul_nonneg (Real.sqrt_nonneg _) (actual_moment_budget_nonneg H δ hδ)

/-- Every JOINT five-axis prefix has a genuine integral bound on the
literal minor set. Even zero-length prefixes are covered by the exact
integer interval representation; no maximum is moved through an integral. -/
theorem actual_original_joint_prefix_control (κ : ℤ) (hκ : κ≠0) (N H : ℕ)
    (hN : 0<N) (B : ℝ) (hB : 0<B) (hs : ((N : ℝ)+1)^3≤B)
    (δ : ℝ) (hδ : 0<δ) :
    JointPrefixControl (volume.restrict (minorDomain N B))
      (originalPrefixIntegralBudget κ H N B δ) (quadraticFiveAxes κ H) (fun _ => 1) := by
  simp only [quadraticFiveAxes,JointPrefixControl,quadraticTimeAxis]
  intro n0 hn0 n1 hn1 n2 hn2 n3 hn3 n4 hn4
  have hpre (u : Coordinates ℤ) (c : ℤ) (n : ℕ) (t : ℝ) := actual_quadratic_prefix u c H n t
  simp only [quadraticTimeAxis] at hpre
  simp_rw [hpre firstDirection 1,hpre secondDirection 1,hpre thirdDirection (-1),
    hpre fourthDirection (-1),hpre fifthDirection (-κ)]
  simp only [one_mul]
  let s (n : ℕ) := Finset.Icc (-(H : ℤ)) (-(H : ℤ)+(n : ℤ)-1)
  have hD : minorDomain N B⊆Set.Icc (-radius N B) (1-radius N B) := by
    intro t ht
    exact ⟨ht.1.1.le,ht.1.2⟩
  have hcont := ((((actual_quadratic_continuous (s n0) 1).mul
    (actual_quadratic_continuous (s n1) 1)).mul (actual_quadratic_continuous (s n2) (-1))).mul
    (actual_quadratic_continuous (s n3) (-1))).mul (actual_quadratic_continuous (s n4) (-κ))
  refine ⟨hcont.continuousOn.integrableOn_Icc.mono_set hD,?_⟩
  have hb := actual_all_original_prefixes κ hκ N H hN B hB hs
    (-(H : ℤ)) (-(H : ℤ)+(n0 : ℤ)-1) (-(H : ℤ)) (-(H : ℤ)+(n1 : ℤ)-1)
    (-(H : ℤ)) (-(H : ℤ)+(n2 : ℤ)-1) (-(H : ℤ)) (-(H : ℤ)+(n3 : ℤ)-1)
    (-(H : ℤ)) (-(H : ℤ)+(n4 : ℤ)-1)
    le_rfl (by omega) le_rfl (by omega) le_rfl (by omega) le_rfl (by omega) le_rfl (by omega) δ hδ
  simpa only [actual_original_rectangle_factorization,originalPrefixIntegralBudget] using hb

end ActualOriginalFiveQuadraticPrefixes318
