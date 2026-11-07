module
public import InertChart318
public import IntegralScaledNorm318
public section
namespace InertLogHom318
open PowerSeries IntegralRingEvaluation318 InertIntegers318 InertChart318 ReciprocalDouble318
open WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
variable (p:ℕ) [Fact p.Prime] (ns:¬∃x:ZMod p,x^2=2)
local notation "R" => Integers p ns
local notation "L" => InertCompletion318.Field p ns
local notation "φ" => embedding p ns
local notation "ι" => padicIntEmbedding p ns
local instance : DecidableEq L := Classical.decEq _

theorem U_injective : Function.Injective (U p ns) := by
  intro a b h
  apply embedding_injective p ns
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out:p.Prime).ne_zero) h

theorem chart_injective (hp:19≤p) (D:R) : Function.Injective (chart p ns hp D) := by
  intro a b h
  apply U_injective p ns
  by_cases ha:U p ns a=0
  · by_cases hb:U p ns b=0
    · exact ha.trans hb.symm
    · simp [chart,point,ha,hb] at h
  by_cases hb:U p ns b=0
  · simp [chart,point,ha,hb] at h
  simp only [chart,point,dite_eq_right ha,dite_eq_right hb] at h
  have hx:1/(U p ns a)^2=1/(U p ns b)^2 := (Point.some.inj h).1
  have hy:V p ns hp D a/(U p ns a)^3=V p ns hp D b/(U p ns b)^3 := (Point.some.inj h).2
  have hs:(U p ns a)^2=(U p ns b)^2 := inv_injective (by simpa only [one_div] using hx)
  have hv:=normalized_square p ns hp D a b hs
  calc
    U p ns a=(1/(U p ns a)^2)*V p ns hp D a/(V p ns hp D a/(U p ns a)^3) := by
      field_simp [ha,V_nonzero p ns hp D a]
    _=(1/(U p ns b)^2)*V p ns hp D b/(V p ns hp D b/(U p ns b)^3) := by rw [hx,hy,hv]
    _=U p ns b := by field_simp [hb,V_nonzero p ns hp D b]

theorem chart_zero (hp:19≤p) (D:R) : chart p ns hp D 0=0 := by
  simp [chart,U,point]

theorem chart_negative (hp:19≤p) (D:R) (t:R) : chart p ns hp D (-t)= -chart p ns hp D t := by
  have hu:U p ns (-t)= -U p ns t := by simp [U]
  have hv:V p ns hp D (-t)=V p ns hp D t :=
    normalized_square p ns hp D _ _ (by rw [hu]; ring)
  simpa only [chart,hu,hv] using point_negative (φ D) (U p ns t) (V p ns hp D t)
    (V_nonzero p ns hp D t) (curve p ns hp D t)

/-- The actual depth-one elliptic subgroup over the completed inert field. -/
@[expose] def formalSubgroup (hp:19≤p) (D:R) : AddSubgroup (E (φ D)).Point where
  carrier:=Set.range (chart p ns hp D)
  zero_mem':=⟨0,chart_zero p ns hp D⟩
  add_mem':=by
    rintro P Q ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨sumParameter p ns hp D ![a,b],(chart_add p ns hp D ![a,b]).symm⟩
  neg_mem':=by
    rintro P ⟨a,rfl⟩
    exact ⟨-a,chart_negative p ns hp D a⟩

@[expose] def parameterOf (hp:19≤p) (D:R) (P:formalSubgroup p ns hp D) : R := Classical.choose P.2

theorem chart_parameterOf (hp:19≤p) (D:R) (P:formalSubgroup p ns hp D) :
    chart p ns hp D (parameterOf p ns hp D P)=P.1 := Classical.choose_spec P.2

theorem parameterOf_chart (hp:19≤p) (D:R) (t:R) :
    parameterOf p ns hp D ⟨chart p ns hp D t,⟨t,rfl⟩⟩=t :=
  chart_injective p ns hp D (chart_parameterOf p ns hp D _)

@[expose] def logarithm (hp:19≤p) (D:R) (P:formalSubgroup p ns hp D) : L :=
  integralValue p ns hp D (parameterOf p ns hp D P)

theorem logarithm_chart (hp:19≤p) (D:R) (t:R) :
    logarithm p ns hp D ⟨chart p ns hp D t,⟨t,rfl⟩⟩=integralValue p ns hp D t := by
  rw [logarithm,parameterOf_chart]

theorem integralValue_eq (hp:19≤p) (D:R) (t:R) : integralValue p ns hp D t=
    -U p ns t*φ (eval R (ArbitraryInertSeries318.H p ns hp D) (t^4)) := by
  have hx:=X_restricted R
  have hH:=ArbitraryInertSeries318.H_restricted p ns hp D
  have he:eval R (ArbitraryInertSeries318.integral p ns hp D) t=
    -t*eval R (ArbitraryInertSeries318.H p ns hp D) (t^4) := by
    change eval R (-X*(ArbitraryInertSeries318.H p ns hp D).subst (X^4)) t=_
    rw [eval_mul R _ _ hx.neg (subst_restricted R _ _ hH (hx.pow 4) (by simp)),
      eval_neg R X,eval_X,eval_subst R _ _ hH (hx.pow 4) (by simp),eval_pow R X hx,eval_X]
  dsimp only [integralValue,U]
  rw [he,map_mul,map_neg]
  ring

theorem integralValue_zero (hp:19≤p) (D:R) : integralValue p ns hp D 0=0 := by
  rw [integralValue_eq]; simp [U]

theorem logarithm_add (hp:19≤p) (D:R) (P Q:formalSubgroup p ns hp D) :
    logarithm p ns hp D (P+Q)=logarithm p ns hp D P+logarithm p ns hp D Q := by
  let a:=parameterOf p ns hp D P
  let b:=parameterOf p ns hp D Q
  have he:parameterOf p ns hp D (P+Q)=sumParameter p ns hp D ![a,b] := by
    apply chart_injective p ns hp D
    rw [chart_parameterOf,←chart_add]
    change P.1+Q.1=chart p ns hp D a+chart p ns hp D b
    rw [chart_parameterOf,chart_parameterOf]
  rw [logarithm,he]
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,logarithm,a,b] using integral_add p ns hp D ![a,b]

/-- This homomorphism is constructed from the convergent full series and
 actual group law, not assumed as an inert formal-log interface. -/
@[expose] def logHom (hp:19≤p) (D:R) : formalSubgroup p ns hp D→+L where
  toFun:=logarithm p ns hp D
  map_zero':=by
    have hz:parameterOf p ns hp D 0=0 := by
      apply chart_injective p ns hp D
      rw [chart_parameterOf,chart_zero]; rfl
    rw [logarithm,hz,integralValue_zero]
  map_add':=logarithm_add p ns hp D

/-- The logarithm preserves the exact reciprocal-parameter norm, including O. -/
theorem integralValue_norm (hp:19≤p) (D:R) (t:R) :
    ‖integralValue p ns hp D t‖=‖U p ns t‖ := by
  rw [integralValue_eq,norm_mul,norm_neg]
  have h:=IntegralScaledNorm318.H_map_norm p hp ι D (padicIntEmbedding_isometry p ns)
    φ (embedding_isometry p ns) (t^4)
  change ‖U p ns t‖*‖φ (eval R (IntegralScaledSeries318.H p hp ι D) (t^4))‖=‖U p ns t‖
  rw [h,mul_one]

theorem logHom_norm (hp:19≤p) (D:R) (P:formalSubgroup p ns hp D) :
    ‖logHom p ns hp D P‖=‖U p ns (parameterOf p ns hp D P)‖ :=
  integralValue_norm p ns hp D _

theorem logHom_zero_iff (hp:19≤p) (D:R) (P:formalSubgroup p ns hp D) :
    logHom p ns hp D P=0 ↔ P=0 := by
  constructor
  · intro h
    have hu:U p ns (parameterOf p ns hp D P)=0 := by
      apply norm_eq_zero.mp
      rw [←logHom_norm,h,norm_zero]
    have ht:parameterOf p ns hp D P=0 := U_injective p ns (by simpa [U] using hu)
    apply Subtype.ext
    rw [←chart_parameterOf p ns hp D P,ht,chart_zero]
    rfl
  · rintro rfl; exact map_zero _

theorem logHom_injective (hp:19≤p) (D:R) : Function.Injective (logHom p ns hp D) := by
  intro P Q h
  apply sub_eq_zero.mp
  apply (logHom_zero_iff p ns hp D (P-Q)).mp
  rw [map_sub,h,sub_self]

/-- Source-facing norm identity for an actual finite subgroup point. No
 independent square-root or ordinate sign is supplied. -/
theorem affine_norm_square (hp:19≤p) (D:R) (P:formalSubgroup p ns hp D)
    (x y:L) (hxy:(E (φ D)).Nonsingular x y) (hP:P.1=Point.some x y hxy) :
    ‖logHom p ns hp D P‖^2=‖1/x‖ := by
  have he:=chart_parameterOf p ns hp D P
  rw [hP] at he
  have hu:U p ns (parameterOf p ns hp D P)≠0 := by
    intro hz
    simp [chart,point,hz] at he
  simp only [chart,point,dite_eq_right hu] at he
  have hx:1/(U p ns (parameterOf p ns hp D P))^2=x := (Point.some.inj he).1
  rw [logHom_norm,←hx]
  simp only [one_div,inv_inv,norm_pow]

/-- Relative reciprocal-abscissa norm bounds become half as large in the
 actual logarithm filtration. -/
theorem reciprocal_gain (hp:19≤p) (D:R)
    (H Q:formalSubgroup p ns hp D) (xH yH xQ yQ:L)
    (hH:(E (φ D)).Nonsingular xH yH) (hQ:(E (φ D)).Nonsingular xQ yQ)
    (hHP:H.1=Point.some xH yH hH) (hQP:Q.1=Point.some xQ yQ hQ)
    (k:ℕ) (hgain:‖1/xQ‖≤‖(p:ℚ_[p])‖^(2*k)*‖1/xH‖) :
    ‖logHom p ns hp D Q‖≤‖(p:ℚ_[p])‖^k*‖logHom p ns hp D H‖ := by
  rw [←affine_norm_square p ns hp D H xH yH hH hHP,
    ←affine_norm_square p ns hp D Q xQ yQ hQ hQP] at hgain
  have hp2:‖(p:ℚ_[p])‖^(2*k)=(‖(p:ℚ_[p])‖^k)^2 := by rw [←pow_mul]; congr 1; omega
  rw [hp2] at hgain
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg (norm_nonneg (p:ℚ_[p])) k)
    (norm_nonneg _))).mp
  simpa only [mul_pow] using hgain

end
end InertLogHom318
#print axioms InertLogHom318.logHom
#print axioms InertLogHom318.logHom_norm
#print axioms InertLogHom318.logHom_injective

#print axioms InertLogHom318.affine_norm_square
#print axioms InertLogHom318.reciprocal_gain
