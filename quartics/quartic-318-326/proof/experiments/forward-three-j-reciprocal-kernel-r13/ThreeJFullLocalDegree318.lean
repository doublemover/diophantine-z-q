module
public import ThreeJOrdinaryOrders318
public section
noncomputable section
open Filter Topology
namespace ThreeJFullLocalDegree318
open ProjectiveLineFieldPoints318 ProjectiveLinePointEquiv318
open ThreeProjectiveJPoints318 ThreeJChartHolomorphy318 ThreeJAnalyticGerms318
open ThreeJActualFiniteOrders318 ThreeJOrdinaryOrders318 ThreeCompactParameter318
set_option maxHeartbeats 1000000

/-- A precise local expression certificate in the original scheme charts:
the germ represents the actual map on a full source-coordinate neighborhood,
and its centered target expression has the specified order. -/
def LocalDegreeCertificate (p : Points (R:=ℚ) (K:=ℂ)) (e : ℕ) : Prop :=
  ∃ (i j : Fin 2) (t : ℂ) (F : ℂ → ℂ), chartPoint (R:=ℚ) i t=p ∧
    AnalyticAt ℂ F t ∧
    (∀ᶠ z in 𝓝 t, mapPoints (chartPoint (R:=ℚ) i z)=chartPoint (R:=ℚ) j (F z)) ∧
    meromorphicOrderAt (fun z => F z-F t) t=(e:ℤ)

lemma finite_nonzero_certificate (t : ℂ) (ht : t ≠ 0) :
    LocalDegreeCertificate (chartPoint (R:=ℚ) 1 t) (finiteOrder t) := by
  refine ⟨1,1,t,J,rfl,ThreeJEllipticOrders318.J_analytic ht,?_,?_⟩
  · filter_upwards [eventually_ne_nhds ht] with z hz
    have hd : Polynomial.aeval z ThreeProjectiveJCertificates318.finiteDenominator ≠ 0 := by
      rw [(finite_evaluations z).2]
      exact pow_ne_zero 3 hz
    rw [finite_formula z hd,←ActualThreeJChartConsumer318.finite_J]
  · have he : (fun z => actualFiniteExpression z-J t) =ᶠ[𝓝 t] (fun z => J z-J t) := by
      filter_upwards [actualFiniteExpression_eq ht] with z hz
      rw [hz]
    rw [←meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds)]
    exact actual_centered_order ht

lemma finite_zero_certificate : LocalDegreeCertificate (chartPoint (R:=ℚ) 1 (0:ℂ)) 3 := by
  refine ⟨1,0,0,finitePole,rfl,finite_cusp_germ.1,exact_cusp_germs.1,?_⟩
  simpa only [finite_cusp_germ.2.1,sub_zero] using finite_cusp_germ.2.2
lemma infinity_certificate : LocalDegreeCertificate (chartPoint (R:=ℚ) 0 (0:ℂ)) 1 := by
  refine ⟨0,0,0,reciprocalPole,rfl,reciprocal_cusp_germ.1,exact_cusp_germs.2.1,?_⟩
  simpa only [reciprocal_cusp_germ.2.1,sub_zero] using reciprocal_cusp_germ.2.2

/-- Every genuine projective complex scheme point is covered, not merely
finite points away from the poles. Orders1,2,3 are complete for this exact map. -/
theorem every_point (p : Points (R:=ℚ) (K:=ℂ)) :
    ∃ e : ℕ, (e=1 ∨ e=2 ∨ e=3) ∧ LocalDegreeCertificate p e := by
  rcases finite_or_infinity p with ⟨t,ht⟩ | hp
  · subst p
    by_cases hz : t=0
    · subst t
      exact ⟨3,Or.inr (Or.inr rfl),finite_zero_certificate⟩
    · refine ⟨finiteOrder t,?_,finite_nonzero_certificate t hz⟩
      unfold finiteOrder
      split_ifs <;> simp
  · subst p
    exact ⟨1,Or.inl rfl,infinity_certificate⟩

/-- Exact finite branch parameters; the finite origin is separately the
order-three cusp, and the reciprocal origin is unramified. -/
theorem finite_ramified_iff (t : ℂ) : finiteOrder t ≠ 1 ↔ t= -243 ∨ D t=0 := by
  unfold finiteOrder
  split_ifs <;> simp_all

/-- All original q-discs retain their independently proved canonical cusp
orders, alongside the exhaustive algebraic-chart local-degree certificates. -/
theorem actual_cusp_orders (c : FiniteCuspEnds318.End 3) :
    AnalyticAt ℂ (ActualThreeJQDiscGerms318.actualQExpression c) 0 ∧
      meromorphicOrderAt (ActualThreeJQDiscGerms318.actualQExpression c) 0=
        (ActualThreeJQDiscGerms318.qOrder c : ℤ) :=
  ActualThreeJQDiscGerms318.actual_q_germ c

end ThreeJFullLocalDegree318
