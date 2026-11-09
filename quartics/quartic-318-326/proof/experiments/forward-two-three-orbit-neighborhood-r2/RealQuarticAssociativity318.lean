module
public import RealQuarticSumAnalytic318
public section
noncomputable section
namespace RealQuarticAssociativity318
open Set ReciprocalGroup318 RealQuarticSumU318 RealQuarticSumAnalytic318
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma sumV_associative_square {D : ℝ} (hD : 0<D) (u v a b c e : ℝ)
    (hv : v^2=1-D*u^4) (hb : b^2=1-D*a^4) (he : e^2=1-D*c^4) :
    (sumV D (sumU D u v a b) (sumV D u v a b) c e)^2 =
      (sumV D u v (sumU D a b c e) (sumV D a b c e))^2 := by
  have hl := sum_curve D (sumU D u v a b) (sumV D u v a b) c e
    (sum_curve D u v a b hv hb (denominator_ne hD u a)) he
    (denominator_ne hD _ _)
  have hr := sum_curve D u v (sumU D a b c e) (sumV D a b c e) hv
    (sum_curve D a b c e hb he (denominator_ne hD a c))
    (denominator_ne hD _ _)
  rw [hl,hr,sumU_associative hD u v a b c e hv hb he]

/-- Global second-coordinate associativity. The entire analytic angle cover
of three full ovals removes the square-root sign ambiguity: both analytic
sides agree with the nonzero value1 at the three identity points. -/
theorem sumV_associative {D : ℝ} (hD : 0<D) (u v a b c e : ℝ)
    (hv : v^2=1-D*u^4) (hb : b^2=1-D*a^4) (he : e^2=1-D*c^4) :
    sumV D (sumU D u v a b) (sumV D u v a b) c e =
      sumV D u v (sumU D a b c e) (sumV D a b c e) := by
  let U (i : Fin 3) (t : Fin 3 → ℝ) := RealQuarticOvalCover318.u D (t i)
  let V (i : Fin 3) (t : Fin 3 → ℝ) := RealQuarticOvalCover318.v (t i)
  have hU (i : Fin 3) (t : Fin 3 → ℝ) : AnalyticAt ℝ (U i) t :=
    (RealQuarticOvalCover318.u_analytic D (t i)).fun_comp
      (f:=fun s : Fin 3 → ℝ => s i) (x:=t) ((ContinuousLinearMap.proj (R:=ℝ) i).analyticAt t)
  have hV (i : Fin 3) (t : Fin 3 → ℝ) : AnalyticAt ℝ (V i) t :=
    (RealQuarticOvalCover318.v_analytic (t i)).fun_comp
      (f:=fun s : Fin 3 → ℝ => s i) (x:=t) ((ContinuousLinearMap.proj (R:=ℝ) i).analyticAt t)
  have hcurve (i : Fin 3) (t : Fin 3 → ℝ) : (V i t)^2=1-D*(U i t)^4 :=
    RealQuarticOvalCover318.oval_equation hD (t i)
  let f (t : Fin 3 → ℝ) := sumV D (sumU D (U 0 t) (V 0 t) (U 1 t) (V 1 t))
    (sumV D (U 0 t) (V 0 t) (U 1 t) (V 1 t)) (U 2 t) (V 2 t)
  let g (t : Fin 3 → ℝ) := sumV D (U 0 t) (V 0 t)
    (sumU D (U 1 t) (V 1 t) (U 2 t) (V 2 t))
    (sumV D (U 1 t) (V 1 t) (U 2 t) (V 2 t))
  have hf : AnalyticOnNhd ℝ f univ := by
    intro t _
    exact sumV_analytic hD
      (sumU_analytic hD (hU 0 t) (hV 0 t) (hU 1 t) (hV 1 t))
      (sumV_analytic hD (hU 0 t) (hV 0 t) (hU 1 t) (hV 1 t))
      (hU 2 t) (hV 2 t)
  have hg : AnalyticOnNhd ℝ g univ := by
    intro t _
    exact sumV_analytic hD (hU 0 t) (hV 0 t)
      (sumU_analytic hD (hU 1 t) (hV 1 t) (hU 2 t) (hV 2 t))
      (sumV_analytic hD (hU 1 t) (hV 1 t) (hU 2 t) (hV 2 t))
  have hs : ∀ t, (f t)^2=(g t)^2 := by
    intro t
    exact sumV_associative_square hD _ _ _ _ _ _ (hcurve 0 t) (hcurve 1 t) (hcurve 2 t)
  have hf0 : f 0=1 := by simp [f,U,V,RealQuarticOvalCover318.u,RealQuarticOvalCover318.v,sumU,sumV]
  have hg0 : g 0=1 := by simp [g,U,V,RealQuarticOvalCover318.u,RealQuarticOvalCover318.v,sumU,sumV]
  have hfg : f=g := analytic_square_identity hf hg hs (hf0.trans hg0.symm) (by rw [hf0]; norm_num)
  obtain ⟨t0,hu0,hv0⟩ := RealQuarticOvalCover318.oval_surjective hD u v hv
  obtain ⟨t1,hu1,hv1⟩ := RealQuarticOvalCover318.oval_surjective hD a b hb
  obtain ⟨t2,hu2,hv2⟩ := RealQuarticOvalCover318.oval_surjective hD c e he
  have hval := congrFun hfg ![t0,t1,t2]
  simpa [f,g,U,V,hu0,hv0,hu1,hv1,hu2,hv2] using hval

end RealQuarticAssociativity318
