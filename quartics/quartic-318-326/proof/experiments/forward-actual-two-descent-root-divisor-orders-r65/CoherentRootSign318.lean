module
public import CoherentSecant318
public import CoherentOrbit318
public import CoherentMultiplePrefix318
public section
noncomputable section
namespace CoherentRootSign318
open ConcreteG8Domain (K D)
open LocalGenerator318 (E)
open GlobalGeneratorPoints318 (R)
open CoherentMultipleCharts318 (u v chartU chartV fixedRoot)
open WeierstrassCurve.Affine
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma u_sub_of_xRep_ne (Q S : E.Point) (hne : Q.xRep≠S.xRep) :
    u (Q-S)*(1+D*(u Q)^2*(u S)^2)=u Q*v S-u S*v Q := by
  cases Q with
  | zero =>
    change u ((0:E.Point)-S)*(1+D*(u 0)^2*(u S)^2)=u 0*v S-u S*v 0
    simp [CoherentMultipleCharts318.u_negative]
  | some x y hx =>
    cases S with
    | zero =>
      change u (Point.some x y hx-(0:E.Point))*(1+D*(u (Point.some x y hx))^2*(u 0)^2)=
        u (Point.some x y hx)*v 0-u 0*v (Point.some x y hx)
      simp
    | some a b ha =>
      have hxa : x≠a := by
        intro he
        apply hne
        simp only [Point.xRep_some,he]
      exact CoherentSecant318.finite_u_sub x y a b hx ha hxa

/-- The coherent subtraction formula on the entire actual integer half-orbit.
The nontorsion proof rules out the equal-abscissa secant exceptions. -/
theorem orbit_subtraction (n h : ℤ) (hn : n≠0) :
    chartU n*(1+D*(chartU (n*h))^2*(chartU (n*(h-1)))^2)=
      chartU (n*h)*chartV (n*(h-1))-chartU (n*(h-1))*chartV (n*h) := by
  have hd : (n*h) • R-(n*(h-1)) • R=n • R := by
    simp only [sub_eq_add_neg,←neg_zsmul,←add_zsmul]
    congr 1
    ring
  have he := u_sub_of_xRep_ne ((n*h) • R) ((n*(h-1)) • R)
    (CoherentOrbit318.adjacent_xRep_ne n h hn)
  rw [hd] at he
  exact he

lemma addition_denominator_ne (U A : K) : 1+D*U^2*A^2≠0 := by
  let σ := ActualQuadraticEmbeddings318.positiveEmbedding
  have hd := RealMultiples318.real_D_gt_one σ
  have hp : 0≤σ D*(σ U)^2*(σ A)^2 :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _)
  intro he
  have hh := congrArg σ he
  simp only [map_add,map_one,map_mul,map_pow,map_zero] at hh
  linarith

lemma root_quotient (U V A B C : K) (hc : V^2=1-D*U^4) (ha : B^2=1-D*A^4)
    (hsub : C*(1+D*U^2*A^2)=U*B-A*V) (hden : A^2-U^2≠0) (hC : C≠0) :
    (U*B+A*V)/(A^2-U^2)= -(1/C) := by
  have hp : (U*B+A*V)*(U*B-A*V)=(U^2-A^2)*(1+D*U^2*A^2) := by
    linear_combination U^2*ha-A^2*hc
  have hm : (U*B+A*V)*C=U^2-A^2 := by
    apply mul_right_cancel₀ (addition_denominator_ne U A)
    calc
      ((U*B+A*V)*C)*(1+D*U^2*A^2)=(U*B+A*V)*(C*(1+D*U^2*A^2)) := by ring
      _ = (U*B+A*V)*(U*B-A*V) := by rw [hsub]
      _ = (U^2-A^2)*(1+D*U^2*A^2) := hp
  field_simp [hden,hC]
  linear_combination hm

/-- Every guarded literal emitted root has the fixed historical sign, for
all common integer indices h. The signed roots can therefore precede prime choice. -/
theorem emitted_root_fixed (n : Fin 4 → ℤ) (h : ℤ) (j : Fin 4) (hn : n j≠0)
    (hg : (RealGuardWitness318.denominator (CoherentMultiplePrefix318.u n h) j).re≠0) :
    RealGuardWitness318.root (CoherentMultiplePrefix318.u n h)
      (CoherentMultiplePrefix318.v n h) j=fixedRoot (n j) := by
  have hden := RealGuardWitness318.denominator_ne (CoherentMultiplePrefix318.u n h) j hg
  have hc := CoherentMultipleCharts318.chart_curve (n j*h)
  have ha := CoherentMultipleCharts318.chart_curve (n j*(h-1))
  rw [CoherentMultipleCharts318.D_eq] at hc ha
  have hC : chartU (n j)≠0 := fun he => hn ((CoherentMultipleCharts318.chartU_zero_iff _).mp he)
  simp only [RealGuardWitness318.denominator,CoherentMultiplePrefix318.u,
    CoherentMultiplePrefix318.parameters,Fin.append_left,Fin.append_right] at hden
  simpa only [RealGuardWitness318.root,RealGuardWitness318.numerator,
    RealGuardWitness318.denominator,CoherentMultiplePrefix318.u,CoherentMultiplePrefix318.v,
    CoherentMultiplePrefix318.parameters,Fin.append_left,Fin.append_right,fixedRoot] using
    root_quotient (chartU (n j*h)) (chartV (n j*h)) (chartU (n j*(h-1)))
      (chartV (n j*(h-1))) (chartU (n j)) hc ha (orbit_subtraction (n j) h hn) hden hC

end CoherentRootSign318
