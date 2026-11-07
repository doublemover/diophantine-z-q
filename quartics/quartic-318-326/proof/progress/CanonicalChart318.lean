module
public import CanonicalRoot318
public section
namespace CanonicalChart318
variable {K : Type*} [Field K]

/-- The local reciprocal chart is constructed from an actual Weierstrass point
and the normalized root, rather than assuming a square root of 1/x. -/
theorem reciprocal_square (D x y v : K) (hx : x≠0) (hy : y≠0)
    (hc : y^2=x^3-D*x) (hv : v^2=1-D/x^2) : (x*v/y)^2*x=1 := by
  have hs : v^2*x^2=x^2-D := by
    apply (eq_div_iff (pow_ne_zero 2 hx)).mp
    calc
      v^2=1-D/x^2 := hv
      _=(x^2-D)/x^2 := by field_simp
  field_simp [hy]
  linear_combination x*hs-hc

theorem reciprocal_coordinates (D x y v : K) (hx : x≠0) (hy : y≠0) (hv0 : v≠0)
    (hc : y^2=x^3-D*x) (hv : v^2=1-D/x^2) :
    let u := x*v/y
    u≠0 ∧ 1/u^2=x ∧ v/u^3=y ∧ v^2=1-D*u^4 := by
  let u := x*v/y
  have hu : u≠0 := div_ne_zero (mul_ne_zero hx hv0) hy
  have hs : u^2*x=1 := reciprocal_square D x y v hx hy hc hv
  have hx' : 1/u^2=x := by
    apply (div_eq_iff (pow_ne_zero 2 hu)).mpr
    linear_combination -hs
  have hy' : v/u^3=y := by
    apply (div_eq_iff (pow_ne_zero 3 hu)).mpr
    have hm : y*u=x*v := by dsimp [u]; field_simp
    calc
      v = v*(u^2*x) := by rw [hs,mul_one]
      _ = (x*v)*u^2 := by ring
      _ = (y*u)*u^2 := congrArg (fun t => t*u^2) hm.symm
      _ = y*u^3 := by ring
  have hfour : u^4=1/x^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hx)).mpr
    calc
      u^4*x^2 = (u^2*x)^2 := by ring
      _ = 1 := by rw [hs,one_pow]
  refine ⟨hu,hx',hy',?_⟩
  change v^2=1-D*u^4
  rw [hfour,hv,mul_one_div]

end CanonicalChart318
#print axioms CanonicalChart318.reciprocal_coordinates
