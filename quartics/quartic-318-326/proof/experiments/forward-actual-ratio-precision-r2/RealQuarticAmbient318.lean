module
public import CoherentMultiplePrefix318
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public section
noncomputable section
namespace RealQuarticAmbient318
open Set
open ConcreteG8Domain (K D)
set_option maxHeartbeats 1000000

/-- Eight oriented charts, both actual real embeddings and both coordinates. -/
abbrev Ambient := (Fin 8 × Fin 2 × Fin 2) → ℝ

@[expose] def embedding (e : Fin 2) : K →+* ℝ :=
  if e=0 then ActualQuadraticEmbeddings318.positiveEmbedding
  else ActualQuadraticEmbeddings318.negativeEmbedding
@[expose] def d (e : Fin 2) : ℝ := embedding e D

lemma d_gt_one (e : Fin 2) : 1<d e := RealMultiples318.real_D_gt_one (embedding e)

/-- The product of the sixteen actual real reciprocal quartic ovals. -/
@[expose] def ovals : Set Ambient := {z | ∀ i e, z (i,e,1)^2=1-d e*z (i,e,0)^4}

lemma ovals_closed : IsClosed ovals := by
  have he : ovals = ⋂ i, ⋂ e, {z : Ambient | z (i,e,1)^2=1-d e*z (i,e,0)^4} := by
    ext z
    simp [ovals]
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro e
  exact isClosed_eq (by fun_prop) (by fun_prop)

lemma coordinate_bound {z : Ambient} (hz : z∈ovals) (i : Fin 8) (e c : Fin 2) :
    |z (i,e,c)|≤1 := by
  have he := hz i e
  have hd := d_gt_one e
  have hu2 := sq_nonneg (z (i,e,0))
  have hu4 := sq_nonneg ((z (i,e,0))^2)
  have hv2 := sq_nonneg (z (i,e,1))
  have hmul : 0≤d e*(z (i,e,0))^4 := mul_nonneg (by linarith) (by positivity)
  have hprod : 0≤(d e-1)*(z (i,e,0))^4 := mul_nonneg (by linarith) (by positivity)
  have hu : (z (i,e,0))^2≤1 := by nlinarith
  have hv : (z (i,e,1))^2≤1 := by nlinarith
  fin_cases c
  · exact (sq_le_one_iff_abs_le_one _).mp hu
  · exact (sq_le_one_iff_abs_le_one _).mp hv

/-- Compactness is proved in the ordinary finite-dimensional real topology. -/
theorem ovals_compact : IsCompact ovals := by
  apply (isCompact_closedBall (0:Ambient) 1).of_isClosed_subset ovals_closed
  intro z hz
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  rintro ⟨i,e,c⟩
  simpa only [Real.norm_eq_abs] using coordinate_bound hz i e c

/-- A coordinate projection is analytic in the existing ambient topology. -/
lemma coordinate_analytic (a : Fin 8 × Fin 2 × Fin 2) (z : Ambient) :
    AnalyticAt ℝ (fun x : Ambient => x a) z :=
  (ContinuousLinearMap.proj (R:=ℝ) a).analyticAt z

/-- Exact real coordinates of the coherent common-integer source charts. -/
@[expose] def orbit (n : Fin 4 → ℤ) (h : ℤ) : Ambient :=
  fun ⟨i,e,c⟩ => if c=0 then embedding e (CoherentMultiplePrefix318.u n h i)
    else embedding e (CoherentMultiplePrefix318.v n h i)

theorem orbit_mem (n : Fin 4 → ℤ) (h : ℤ) : orbit n h∈ovals := by
  intro i e
  have hc := congrArg (embedding e) (CoherentMultiplePrefix318.curves n h i)
  rw [CoherentMultipleCharts318.D_eq] at hc
  simpa [orbit,d] using hc

/-- No group or analytic-submanifold structure is asserted for this closure. -/
@[expose] def orbitClosure (n : Fin 4 → ℤ) : Set Ambient := closure (range (orbit n))

theorem orbitClosure_subset (n : Fin 4 → ℤ) : orbitClosure n⊆ovals := by
  apply closure_minimal
  · rintro z ⟨h,rfl⟩
    exact orbit_mem n h
  · exact ovals_closed

theorem orbitClosure_compact (n : Fin 4 → ℤ) : IsCompact (orbitClosure n) :=
  ovals_compact.of_isClosed_subset isClosed_closure (orbitClosure_subset n)

end RealQuarticAmbient318
