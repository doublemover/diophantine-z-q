module
public import ThreeJModuliOpen318
public section
noncomputable section
namespace ThreeNormalizedInverse318
set_option maxHeartbeats 1500000
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma rational_unit (q : ℚ) (hq : q ≠ 0) : IsUnit (algebraMap ℚ R q) :=
  (isUnit_iff_ne_zero.mpr hq).map (algebraMap ℚ R)
lemma positive_nat_unit (n : ℕ) (hn : n ≠ 0) : IsUnit (n:R) := by
  simpa only [map_natCast] using (rational_unit (R:=R) n (Nat.cast_ne_zero.mpr hn))

variable (k x : R)
@[expose] def relation : R := x^4-6*k*x^2-8*k*x-3*k^2
@[expose] def numerator : R := x^2-k
@[expose] def denominator : R := 9*k-x^2

/-- Polynomial Bezout certificates work over arbitrary Q-algebras,
including nonfields and nonreduced rings. -/
lemma numerator_bezout :
    numerator k x * (-5*k^2+k*x^2+5*k*x+8*k-x^3)-8*k^2*(k-1)=
      (k-x)*relation k x := by unfold numerator relation; ring
lemma denominator_bezout :
    denominator k x * (9*k^2+3*k*x^2+3*k*x-8*k+x^3)-72*k^2*(k-1)=
      (-3*k-x)*relation k x := by unfold denominator relation; ring
lemma root_bezout : x*(x^3-6*k*x-8*k)-3*k^2=relation k x := by
  unfold relation; ring

variable (hk : IsUnit k) (hk1 : IsUnit (k-1)) (hq : relation k x=0)
include hk hk1 hq in
lemma numerator_unit : IsUnit (numerator k x) := by
  have he : numerator k x * (-5*k^2+k*x^2+5*k*x+8*k-x^3)=8*k^2*(k-1) := by
    have h := numerator_bezout k x
    rw [hq,mul_zero] at h
    exact sub_eq_zero.mp h
  exact (IsUnit.mul_iff.mp (he.symm ▸ ((positive_nat_unit 8 (by decide)).mul (hk.pow 2)).mul hk1)).1
include hk hk1 hq in
lemma denominator_unit : IsUnit (denominator k x) := by
  have he : denominator k x * (9*k^2+3*k*x^2+3*k*x-8*k+x^3)=72*k^2*(k-1) := by
    have h := denominator_bezout k x
    rw [hq,mul_zero] at h
    exact sub_eq_zero.mp h
  exact (IsUnit.mul_iff.mp (he.symm ▸ ((positive_nat_unit 72 (by decide)).mul (hk.pow 2)).mul hk1)).1
include hk hq in
lemma root_unit : IsUnit x := by
  have he : x*(x^3-6*k*x-8*k)=3*k^2 := by
    have h := root_bezout k x
    rw [hq] at h
    exact sub_eq_zero.mp h
  exact (IsUnit.mul_iff.mp (he.symm ▸ (positive_nat_unit 3 (by decide)).mul (hk.pow 2))).1

@[expose] def w : R := ↑((denominator_unit k x hk hk1 hq).unit⁻¹)
lemma denominator_inverse : denominator k x*w k x hk hk1 hq=1 :=
  (denominator_unit k x hk hk1 hq).mul_val_inv
@[expose] def parameter : R := 243*numerator k x*w k x hk hk1 hq
lemma parameter_unit : IsUnit (parameter k x hk hk1 hq) :=
  ((positive_nat_unit 243 (by decide)).mul (numerator_unit k x hk hk1 hq)).mul
    (Units.isUnit _)

local notation "u" => 243*numerator k x
local notation "b" => denominator k x
local notation "v" => w k x hk hk1 hq
local notation "t" => parameter k x hk hk1 hq
include hq in
lemma homogeneous_D : u^2-486*u*b-19683*b^2=1259712*x*k := by
  have h := hq
  unfold numerator denominator relation at *
  linear_combination 157464*h
include hq in
lemma homogeneous_X : 3*(u+27*b)*(u+243*b)=x*(u^2-486*u*b-19683*b^2) := by
  have h := hq
  unfold numerator denominator relation at *
  linear_combination -157464*x*h
include hq in
lemma homogeneous_J : (u+27*b)*(u+243*b)^3*(k-1)=1728*k*u^3*b := by
  have h := hq
  unfold numerator denominator relation at *
  linear_combination 24794911296*k*(-3*k^2-6*k*x^2+8*k*x+x^4)*h

lemma shifted (c : R) : t+c=(u+c*b)*v := by
  have h := denominator_inverse k x hk hk1 hq
  unfold parameter
  linear_combination -c*h
lemma D_expression : t^2-486*t-19683=(u^2-486*u*b-19683*b^2)*v^2 := by
  have h := denominator_inverse k x hk hk1 hq
  unfold parameter
  linear_combination (486*u*v+19683*b*v+19683)*h
lemma D_parameter : t^2-486*t-19683=1259712*x*k*v^2 := by
  rw [D_expression,homogeneous_D k x hq]
lemma D_unit : IsUnit (t^2-486*t-19683) := by
  rw [D_parameter]
  exact (((positive_nat_unit 1259712 (by decide)).mul (root_unit k x hk hq)).mul hk).mul
    ((Units.isUnit _).pow 2)
lemma X_parameter : x*(t^2-486*t-19683)=3*(t+27)*(t+243) := by
  rw [D_expression,shifted k x hk hk1 hq 27,shifted k x hk hk1 hq 243]
  linear_combination -(homogeneous_X k x hq)*v^2
lemma J_parameter : (t+27)*(t+243)^3*(k-1)=1728*k*t^3 := by
  rw [shifted k x hk hk1 hq 27,shifted k x hk hk1 hq 243]
  have he := homogeneous_J k x hq
  have hi := denominator_inverse k x hk hk1 hq
  unfold parameter
  linear_combination he*v^4+1728*k*u^3*v^3*hi

end ThreeNormalizedInverse318
