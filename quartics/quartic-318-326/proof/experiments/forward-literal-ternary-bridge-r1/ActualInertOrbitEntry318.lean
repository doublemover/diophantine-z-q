module
public import GeneralSplitDetectorAccess318
public import InertQuadratic318
public section
noncomputable section
namespace ActualInertOrbitEntry318
open ConcreteG8Domain (K D pair i)
open InertCompletion318 InertQuadratic318
open CoherentMultipleCharts318 (chartU chartV)
open GlobalGeneratorPoints318 (R)
open ValuativeOrbitBounds318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime] (ns : ¬∃ x : ZMod p, x^2=2)
local notation "L" => InertCompletion318.Field p ns
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq L := Classical.decEq L

/-- Properness of the actual inert completion is constructed from its
proved isometric Qp² coordinates, not assumed from an unproved finite-residue
comparison with another valuation ring. -/
instance actual_properSpace : ProperSpace L where
  isCompact_closedBall x r := by
    obtain ⟨z,rfl⟩ := coordinates_surjective p ns x
    have he : Metric.closedBall (coordinates p ns z) r=
        coordinates p ns '' Metric.closedBall z r := by
      ext y
      constructor
      · intro hy
        obtain ⟨t,rfl⟩ := coordinates_surjective p ns y
        refine ⟨t,?_,rfl⟩
        simpa only [Metric.mem_closedBall,(coordinates_isometry p ns).dist_eq] using hy
      · rintro ⟨t,ht,rfl⟩
        simpa only [Metric.mem_closedBall,(coordinates_isometry p ns).dist_eq] using ht
    rw [he]
    exact (isCompact_closedBall z r).image (coordinates_continuous p ns)

lemma nonarchimedean : IsNonarchimedean (NormedField.toAbsoluteValue L) :=
  IsUltrametricDist.isNonarchimedean_norm

lemma coefficient_bound : Bound (InertPlace318.place p ns) 0 D := by
  have hi : Bound (InertPlace318.place p ns) 0 i := by rw [Bound,InertPlace318.place_i]
  have he := bsquare (InertPlace318.place p ns)
    (bsub _ (bnat (InertPlace318.place p ns) 3) hi)
  simpa only [D,mul_zero] using he

lemma coefficient_integral : ‖embedding p ns D‖≤1 := by
  have he := (norm_bound_iff p ns D 0).mpr (coefficient_bound p ns)
  simpa only [neg_zero,zpow_zero] using he

lemma coefficient_ne : embedding p ns D≠0 := by
  apply (map_ne_zero_iff (embedding p ns) (embedding p ns).injective).mpr
  intro he
  have hr := congrArg QuadraticAlgebra.re he
  norm_num [D,i,pair,pow_succ] at hr

lemma positive_depth (x : K) (hx : ‖embedding p ns x‖<1) :
    (1:WithTop ℤ)≤InertPlace318.place p ns x := by
  change ‖embedding p ns (pair x.re x.im)‖<1 at hx
  rw [norm_pair,max_lt_iff] at hx
  change (1:WithTop ℤ)≤min (ConcretePadic318.rationalPlace p x.re)
    (ConcretePadic318.rationalPlace p x.im)
  rw [PadicDetectorCoefficients318.rational_embedding,PadicDetectorCoefficients318.rational_embedding]
  exact le_min (ActualSplitOrbitEntry318.positive_depth p _ hx.1)
    (ActualSplitOrbitEntry318.positive_depth p _ hx.2)

/-- The same compact formal-quotient argument enters the actual inert
completion for the literal half point R, then returns the original K-valued
positive oriented chart. No split embedding is used here. -/
theorem actual_entry : ∃ N : ℕ, 0<N ∧ Near (InertPlace318.place p ns) 1
    (chartU (N:ℤ)) (chartV (N:ℤ)) := by
  obtain ⟨N,hN,hformal⟩ := CompactLocalPointCoding318.orbit_entry (nonarchimedean p ns)
    (embedding p ns D) (coefficient_ne p ns) (coefficient_integral p ns)
    (ShortCurveBaseChange318.pointMap (embedding p ns) D R)
  have hmap : ShortCurveBaseChange318.pointMap (embedding p ns) D ((N:ℤ) • R)∈
      AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue L)
        (nonarchimedean p ns) (embedding p ns D) (coefficient_integral p ns) := by
    simpa only [map_zsmul,natCast_zsmul] using hformal
  obtain ⟨hu,hv⟩ := FormalPoleCoherentChart318.actual_chart (embedding p ns)
    (NormedField.toAbsoluteValue L) (nonarchimedean p ns)
    (coefficient_integral p ns) ((N:ℤ) • R) hmap
  exact ⟨N,hN,positive_depth p ns _ hu,positive_depth p ns _ hv⟩

theorem actual_precision : ∃ N : ℕ, 0<N ∧ ∀ (e : ℕ) (m : ℤ),
    Near (InertPlace318.place p ns) ((e:ℤ)+1)
      (chartU ((p:ℤ)^e*N*m)) (chartV ((p:ℤ)^e*N*m)) := by
  obtain ⟨N,hN,hentry⟩ := actual_entry p ns
  refine ⟨N,hN,ValuativeOrbitMultiples318.prime_power_multiples
    (InertPlace318.place p ns) p ?_ N (coefficient_bound p ns) hentry⟩
  rw [Bound,InertPlace318.place_prime]
  exact le_rfl

/-- The actual inert valuation is the minimum of the two original rational
coefficient valuations. Thus one constructed entry gives all four coordinate
errors, uniformly over the later signed multiplier. -/
theorem error_bounds : ∃ N : ℕ, 0<N ∧ ∀ (e : ℕ) (m : ℤ),
    ‖ActualOrbitLocalFilter318.error p ((p:ℤ)^e*N*m)‖≤((p:ℝ)⁻¹)^e := by
  obtain ⟨N,hN,hprecision⟩ := actual_precision p ns
  refine ⟨N,hN,?_⟩
  intro e m
  obtain ⟨hu,hv⟩ := hprecision e m
  have hle : (e:WithTop ℤ)≤(((e:ℤ)+1:ℤ):WithTop ℤ) := by exact_mod_cast (show (e:ℤ)≤e+1 by omega)
  change (((e:ℤ)+1:ℤ):WithTop ℤ)≤min
    (ConcretePadic318.rationalPlace p (chartU ((p:ℤ)^e*N*m)).re)
    (ConcretePadic318.rationalPlace p (chartU ((p:ℤ)^e*N*m)).im) at hu
  change (((e:ℤ)+1:ℤ):WithTop ℤ)≤min
    (ConcretePadic318.rationalPlace p (chartV ((p:ℤ)^e*N*m)-1).re)
    (ConcretePadic318.rationalPlace p (chartV ((p:ℤ)^e*N*m)-1).im) at hv
  have hur := hle.trans ((le_min_iff.mp hu).1)
  have hui := hle.trans ((le_min_iff.mp hu).2)
  have hvr := hle.trans ((le_min_iff.mp hv).1)
  have hvi := hle.trans ((le_min_iff.mp hv).2)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  fin_cases j
  · exact ActualOrbitLocalFilter318.norm_of_depth p e _ hur
  · exact ActualOrbitLocalFilter318.norm_of_depth p e _ hui
  · exact ActualOrbitLocalFilter318.norm_of_depth p e _ hvr
  · exact ActualOrbitLocalFilter318.norm_of_depth p e _ hvi

end ActualInertOrbitEntry318
