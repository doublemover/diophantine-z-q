module
public import ArbitraryInertSeries318
public import IntegralScaledBounds318
public import IntegralLine318
public import ReciprocalGroup318
public section
namespace InertChart318
open PowerSeries IntegralRingEvaluation318 InertIntegers318 ReciprocalDouble318 ReciprocalGroup318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
variable (p:ℕ) [Fact p.Prime] (ns:¬∃x:ZMod p,x^2=2)
local notation "R" => Integers p ns
local notation "L" => InertCompletion318.Field p ns
local notation "φ" => embedding p ns
local notation "ι" => padicIntEmbedding p ns
local instance : DecidableEq L := Classical.decEq _

@[expose] def U (t:R) : L := (p:L)*φ t
@[expose] def V (hp:19≤p) (D:R) (t:R) : L :=
  φ (eval R (ArbitraryInertSeries318.branch p ns hp D) t)
@[expose] def integralValue (hp:19≤p) (D:R) (t:R) : L :=
  (p:L)*φ (eval R (ArbitraryInertSeries318.integral p ns hp D) t)
@[expose] def sumParameter (hp:19≤p) (D:R) (z:Fin 2→R) : R :=
  eval R (FormalLine318.F (ArbitraryInertSeries318.parameter p ns D)
    (ArbitraryInertSeries318.branch p ns hp D) z) 1

theorem parameter_small (D:R) : ‖ArbitraryInertSeries318.parameter p ns D‖<1 :=
  (IntegralScaledBounds318.parameter_norm p ι D (padicIntEmbedding_isometry p ns)).trans_lt
    (ScaledDecay318.ratio_lt_one p 4 (by decide))

theorem parameter_embedding (D:R) : φ (ArbitraryInertSeries318.parameter p ns D)=φ D*(p:L)^4 := by
  simp [ArbitraryInertSeries318.parameter,IntegralScaledSeries318.parameter]

theorem curve (hp:19≤p) (D:R) (t:R) : (V p ns hp D t)^2=1-φ D*(U p ns t)^4 := by
  have hh:=IntegralLine318.evaluated_curve R φ (embedding_injective p ns)
    (ArbitraryInertSeries318.parameter p ns D) (ArbitraryInertSeries318.branch p ns hp D)
    (ArbitraryInertSeries318.branch_restricted p ns hp D)
    (ArbitraryInertSeries318.map_branch p ns hp D) t
  have h:=congrArg φ hh
  simp only [map_pow,map_sub,map_one,map_mul,parameter_embedding] at h
  dsimp only [V,U]
  rw [h]
  ring

theorem V_near_one (hp:19≤p) (D:R) (t:R) : ‖V p ns hp D t-1‖<1 :=
  IntegralScaledBounds318.branch_map_near_one p hp ι D (padicIntEmbedding_isometry p ns)
    φ (embedding_isometry p ns) t

theorem V_nonzero (hp:19≤p) (D:R) (t:R) : V p ns hp D t≠0 :=
  IntegralScaledBounds318.branch_map_ne_zero p hp ι D (padicIntEmbedding_isometry p ns) φ t

theorem norm_two (hp:19≤p) : ‖(2:L)‖=1 := by
  have h:=InertCompletion318.norm_ratCast p ns (2:ℚ)
  norm_cast at h
  rw [h]
  exact JTail318.norm_nat_unit p 2 (by decide) (by omega)

theorem roots_unique (hp:19≤p) (a b:L) (hs:a^2=b^2)
    (ha:‖a-1‖<1) (hb:‖b-1‖<1) : a=b := by
  have hnear:‖(a-1)+(b-1)‖<1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  have hsum:a+b≠0 := by
    intro hz
    have he:(a-1)+(b-1)=-(2:L) := by linear_combination hz
    rw [he,norm_neg,norm_two p ns hp] at hnear
    exact lt_irrefl _ hnear
  have hmul:(a-b)*(a+b)=0 := by linear_combination hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hsum)

theorem normalized_zero (hp:19≤p) (D:R) (t:R) (ht:U p ns t=0) : V p ns hp D t=1 := by
  apply roots_unique p ns hp _ 1
  · rw [curve,ht]; ring
  · exact V_near_one p ns hp D t
  · simp

theorem normalized_square (hp:19≤p) (D:R) (s t:R) (hst:(U p ns s)^2=(U p ns t)^2) :
    V p ns hp D s=V p ns hp D t := by
  apply roots_unique p ns hp _ _ _ (V_near_one p ns hp D s) (V_near_one p ns hp D t)
  rw [curve,curve]
  have h4:(U p ns s)^4=(U p ns t)^4 := by
    calc
      _=((U p ns s)^2)^2 := by ring
      _=((U p ns t)^2)^2 := by rw [hst]
      _=_ := by ring
  rw [h4]

theorem denominator_nonzero (hp:19≤p) (D:R) (z:Fin 2→R) :
    1+φ D*(U p ns (z 0))^2*(U p ns (z 1))^2≠0 := by
  have hsmall:=IntegralLine318.parameter_small R (ArbitraryInertSeries318.parameter p ns D)
    (parameter_small p ns D) z
  have he:φ ((ArbitraryInertSeries318.parameter p ns D)*(z 0)^2*(z 1)^2)=
    φ D*(U p ns (z 0))^2*(U p ns (z 1))^2 := by
    simp only [map_mul,map_pow,parameter_embedding,U]; ring
  have hn:‖φ D*(U p ns (z 0))^2*(U p ns (z 1))^2‖<1 := by
    rw [←he]
    exact hsmall
  intro hz
  have hid:φ D*(U p ns (z 0))^2*(U p ns (z 1))^2= -1 := by linear_combination hz
  rw [hid,norm_neg,norm_one] at hn
  exact lt_irrefl _ hn

theorem sumU_eq (hp:19≤p) (D:R) (z:Fin 2→R) :
    sumU (φ D) (U p ns (z 0)) (V p ns hp D (z 0)) (U p ns (z 1)) (V p ns hp D (z 1))=
      U p ns (sumParameter p ns hp D z) := by
  have h:=IntegralLine318.evaluated_parameter R φ
    (ArbitraryInertSeries318.parameter p ns D) (parameter_small p ns D)
    (ArbitraryInertSeries318.branch p ns hp D) (ArbitraryInertSeries318.branch_restricted p ns hp D) z
  change φ (sumParameter p ns hp D z)=_ at h
  rw [parameter_embedding] at h
  dsimp only [U]
  rw [h]
  dsimp only [sumU,V]
  have hd:φ D*((p:L)*φ (z 0))^2*((p:L)*φ (z 1))^2=
    (φ D*(p:L)^4)*φ (z 0)^2*φ (z 1)^2 := by ring
  rw [hd]
  ring

theorem sumV_eq (hp:19≤p) (D:R) (z:Fin 2→R) :
    sumV (φ D) (U p ns (z 0)) (V p ns hp D (z 0)) (U p ns (z 1)) (V p ns hp D (z 1))=
      V p ns hp D (sumParameter p ns hp D z) := by
  have h:=IntegralLine318.evaluated_ordinate R φ (embedding_injective p ns)
    (ArbitraryInertSeries318.parameter p ns D) (parameter_small p ns D)
    (ArbitraryInertSeries318.branch p ns hp D) (ArbitraryInertSeries318.branch_restricted p ns hp D)
    (ArbitraryInertSeries318.map_branch p ns hp D) z
  change V p ns hp D (sumParameter p ns hp D z)=_ at h
  rw [parameter_embedding] at h
  rw [h]
  dsimp only [sumV,U,V]
  congr 1 <;> ring

@[expose] def chart (hp:19≤p) (D:R) (t:R) : (E (φ D)).Point :=
  point (φ D) (U p ns t) (V p ns hp D t) (V_nonzero p ns hp D t) (curve p ns hp D t)

theorem chart_add (hp:19≤p) (D:R) (z:Fin 2→R) :
    chart p ns hp D (z 0)+chart p ns hp D (z 1)=chart p ns hp D (sumParameter p ns hp D z) := by
  have hout:sumV (φ D) (U p ns (z 0)) (V p ns hp D (z 0)) (U p ns (z 1)) (V p ns hp D (z 1))≠0 := by
    rw [sumV_eq]; exact V_nonzero p ns hp D _
  have h:=actual_add (φ D) (U p ns (z 0)) (V p ns hp D (z 0)) (U p ns (z 1)) (V p ns hp D (z 1))
    (V_nonzero p ns hp D _) (V_nonzero p ns hp D _)
    (curve p ns hp D _) (curve p ns hp D _)
    (normalized_zero p ns hp D _) (normalized_zero p ns hp D _)
    (normalized_square p ns hp D _ _) (denominator_nonzero p ns hp D z) hout
  simpa only [chart,sumU_eq p ns hp D z,sumV_eq p ns hp D z] using h

theorem integral_add (hp:19≤p) (D:R) (z:Fin 2→R) :
    integralValue p ns hp D (sumParameter p ns hp D z)=
      integralValue p ns hp D (z 0)+integralValue p ns hp D (z 1) := by
  have h:=IntegralLine318.evaluated_addition R φ (embedding_injective p ns)
    (ArbitraryInertSeries318.parameter p ns D) (parameter_small p ns D)
    (ArbitraryInertSeries318.integral p ns hp D) (ArbitraryInertSeries318.branch p ns hp D)
    (ArbitraryInertSeries318.integral_restricted p ns hp D)
    (ArbitraryInertSeries318.branch_restricted p ns hp D)
    (ArbitraryInertSeries318.map_integral p ns hp D) (ArbitraryInertSeries318.map_branch p ns hp D) z
  have hh:=congrArg (fun a:R=>(p:L)*φ a) h
  simpa only [integralValue,sumParameter,map_add,mul_add] using hh

end
end InertChart318
#print axioms InertChart318.chart_add
#print axioms InertChart318.integral_add
