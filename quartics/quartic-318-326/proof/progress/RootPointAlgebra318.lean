module
public import KummerAlgebra318
public section
namespace RootPointAlgebra318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] noncomputable def ordinateFactor (u v t w : K) : K :=
  ((u^2+t^2)*v*w+2*u*t*(1-D*u^2*t^2))/(t^2-u^2)^2

/-- The reversed reciprocal root has an explicit square-abscissa ordinate
factor, including the u=0 or t=0 identity-chart boundaries. -/
theorem root_factor_curve (u v t w h : K)
    (hu : v^2=1-D*u^4) (ht : w^2=1-D*t^4)
    (hd : t^2-u^2≠0) (hh : (t^2-u^2)*h=u*w+t*v) :
    (ordinateFactor u v t w)^2=h^4-D := by
  have hid : ((u^2+t^2)*v*w+2*u*t*(1-D*u^2*t^2))^2-
      (u*w+t*v)^4+D*(t^2-u^2)^4=0 := by
    linear_combination
      (D*t^4*u^4-t^4*v^2+t^4*w^2-t^4-4*t^3*u*v*w-4*t^2*u^2*w^2+u^4*w^2)*hu +
      (4*D*t^2*u^6-D*u^8+t^4-4*t^2*u^2-4*t*u^3*v*w-u^4*w^2)*ht
  have he : h=(u*w+t*v)/(t^2-u^2) := (eq_div_iff hd).mpr (by simpa [mul_comm] using hh)
  rw [he]
  dsimp [ordinateFactor]
  field_simp [hd]
  linear_combination hid

/-- A square-abscissa point on the actual real quadratic curve cannot have
zero square root. This uses rational-coordinate positivity, not a sign choice. -/
theorem square_root_nonzero (h j : K) (hj : j^2=h^4-D) : h≠0 := by
  intro hz
  have hre := congrArg QuadraticAlgebra.re hj
  simp only [hz,zero_pow (by decide : 4≠0),zero_sub] at hre
  obtain ⟨a,b⟩ := j
  norm_num [D,i,pair,pow_succ] at hre
  nlinarith [sq_nonneg a,sq_nonneg b]

theorem discriminant_nonzero : E.Δ≠0 := by
  have hd : D≠0 := (RamifiedTwo318.place.ne_top_iff).mp (by rw [RamifiedTwo318.place_D]; simp)
  have he : E.Δ=64*D^3 := by
    simp [E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈]
    ring
  rw [he]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hd)

theorem square_point (h j : K) (hj : j^2=h^4-D) : E.Nonsingular (h^2) (h*j) := by
  apply (equation_iff_nonsingular_of_Δ_ne_zero discriminant_nonzero).mp
  rw [equation_iff]
  simp only [E,zero_mul,mul_zero,add_zero]
  linear_combination h^2*hj

/-- A genuine finite nonidentity Mathlib point is reconstructed from the
literal reciprocal difference data, with no nonzero u or t assumption. -/
theorem root_point (u v t w h : K)
    (hu : v^2=1-D*u^4) (ht : w^2=1-D*t^4)
    (hd : t^2-u^2≠0) (hh : (t^2-u^2)*h=u*w+t*v) :
    h≠0 ∧ E.Nonsingular (h^2) (h*ordinateFactor u v t w) := by
  have hc := root_factor_curve u v t w h hu ht hd hh
  exact ⟨square_root_nonzero h _ hc,square_point h _ hc⟩

theorem factor_of_square_point (h y : K) (hh : h≠0) (hns : E.Nonsingular (h^2) y) :
    ∃j:K,j^2=h^4-D ∧ h*j=y := by
  have hc : y^2=h^6-D*h^2 := by
    have he := hns.1
    rw [equation_iff] at he
    have hp : (h^2)^3=h^6 := by ring
    simpa only [E,zero_mul,mul_zero,add_zero,neg_mul,hp,sub_eq_add_neg] using he
  refine ⟨y/h,?_,?_⟩
  · field_simp [hh]
    linear_combination hc
  · field_simp [hh]

end RootPointAlgebra318
