module
public import InertLogHom318
public import IntegralSquareRoot318
public import CanonicalChart318
public section
namespace InertMembership318
open PowerSeries IntegralRingEvaluation318 InertIntegers318 InertChart318 InertLogHom318
open ReciprocalDouble318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
variable (p:ℕ) [Fact p.Prime] (ns:¬∃x:ZMod p,x^2=2)
local notation "R" => Integers p ns
local notation "L" => InertCompletion318.Field p ns
local notation "φ" => embedding p ns
local notation "ι" => padicIntEmbedding p ns
local instance : DecidableEq L := Classical.decEq _

theorem norm_prime : ‖(p:L)‖=‖(p:ℚ_[p])‖ := by
  have h:=InertCompletion318.norm_ratCast p ns (p:ℚ)
  simpa only [Rat.cast_natCast] using h

/-- Construct the needed positive local root from the full B-series at an
 arbitrary integral argument. No inert square-root existence is assumed. -/
theorem reciprocal_root (hp:19≤p) (D:R) (x:L) (hx:x≠0)
    (hf:‖1/x‖≤‖(p:ℚ_[p])‖^2) :
    ∃a:L,a^2=1-φ D/x^2 ∧ ‖a-1‖<1 ∧ ‖a‖=1 := by
  have hp0:(p:L)≠0:=Nat.cast_ne_zero.mpr (Fact.out:p.Prime).ne_zero
  have hnorm:‖(1/x)/(p:L)^2‖≤1 := by
    rw [norm_div,norm_pow,norm_prime]
    exact (div_le_one (pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out:p.Prime).ne_zero)) 2)).mpr hf
  let t:R:=⟨(1/x)/(p:L)^2,hnorm⟩
  let a:R:=IntegralSquareRoot318.root p hp ι D (t^2)
  refine ⟨φ a,?_,?_,?_⟩
  · have h:=congrArg φ (IntegralSquareRoot318.root_square p hp ι D
      (padicIntEmbedding_isometry p ns) (t^2))
    change (φ a)^2=1-φ D/x^2
    simp only [map_pow,map_sub,map_one,map_mul] at h
    have hparam:φ (IntegralScaledSeries318.parameter p D)=φ D*(p:L)^4 := by
      simp [IntegralScaledSeries318.parameter]
    rw [hparam] at h
    have ht:φ t=(1/x)/(p:L)^2:=rfl
    rw [ht] at h
    convert h using 1 <;> field_simp [hx,hp0] <;> ring
  · rw [IntegralScaledBounds318.norm_map_sub_one φ (embedding_isometry p ns)]
    exact (IntegralSquareRoot318.root_error p hp ι D (padicIntEmbedding_isometry p ns) (t^2)).trans_lt
      (ScaledDecay318.ratio_lt_one p 4 (by decide))
  · exact IntegralSquareRoot318.root_norm p hp ι D (padicIntEmbedding_isometry p ns) (t^2)

/-- Every actual affine point with reciprocal abscissa at depth at least2
 belongs to the actual depth-one logarithm subgroup. Ordinate nonvanishing
 and the local reciprocal square root are consequences, not premises. -/
theorem affine_mem (hp:19≤p) (D:R) (x y:L) (hx:x≠0)
    (hc:y^2=x^3-φ D*x) (h:(E (φ D)).Nonsingular x y)
    (hf:‖1/x‖≤‖(p:ℚ_[p])‖^2) :
    Point.some x y h∈formalSubgroup p ns hp D := by
  obtain ⟨a,ha,hanear,hanorm⟩:=reciprocal_root p ns hp D x hx hf
  have ha0:a≠0:=by intro he; rw [he,norm_zero] at hanorm; exact zero_ne_one hanorm
  have hy:y≠0 := by
    intro hy
    have he:1-φ D/x^2=0 := by
      have hh:x*(x^2-φ D)=0 := by rw [hy] at hc; linear_combination -hc
      have hxD:x^2=φ D := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hx)
      rw [←hxD,div_self (pow_ne_zero 2 hx),sub_self]
    rw [he] at ha
    exact (pow_ne_zero 2 ha0) ha
  let u:=x*a/y
  have hu:=CanonicalChart318.reciprocal_coordinates (φ D) x y a hx hy ha0 hc ha
  change u≠0 ∧ 1/u^2=x ∧ a/u^3=y ∧ a^2=1-φ D*u^4 at hu
  have husq:‖u‖^2=‖1/x‖ := by
    rw [←hu.2.1]
    simp only [one_div,inv_inv,norm_pow]
  have hun:‖u‖≤‖(p:ℚ_[p])‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [husq]; exact hf
  have hp0:(p:L)≠0:=Nat.cast_ne_zero.mpr (Fact.out:p.Prime).ne_zero
  have htNorm:‖u/(p:L)‖≤1 := by
    rw [norm_div,norm_prime]
    exact (div_le_one (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out:p.Prime).ne_zero))).mpr hun
  let t:R:=⟨u/(p:L),htNorm⟩
  have hut:U p ns t=u := by dsimp [U,t,embedding]; field_simp [hp0]
  have hvt:V p ns hp D t=a := by
    apply roots_unique p ns hp _ _ _ (V_near_one p ns hp D t) hanear
    rw [curve,hut,hu.2.2.2]
  refine ⟨t,?_⟩
  simp only [chart,point,hut,hvt,dite_eq_right hu.1,hu.2.1,hu.2.2.1]

end
end InertMembership318
#print axioms InertMembership318.reciprocal_root
#print axioms InertMembership318.affine_mem
