module
public import PositiveUnitSquare318
public section
namespace EuclideanSqrtTwo318
open ConcreteG8Domain AnchorNorm318
set_option maxHeartbeats 0
noncomputable section
abbrev O := Zsqrtd (2:ℤ)

@[expose] def toK : O →+* K where
  toFun u:=pair u.re u.im
  map_zero':=by ext <;> simp [pair]
  map_one':=by ext <;> simp [pair]
  map_add' u v:=by ext <;> simp [pair]
  map_mul' u v:=by
    rw [pair_product]
    ext <;> simp [pair,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring

theorem toK_pair (u:O) : toK u=pair u.re u.im := rfl

theorem toK_injective : Function.Injective toK := by
  intro u v h
  have hr:=congrArg QuadraticAlgebra.re h
  have hi:=congrArg QuadraticAlgebra.im h
  change (u.re:ℚ)=(v.re:ℚ) at hr
  change (u.im:ℚ)=(v.im:ℚ) at hi
  exact Zsqrtd.ext (by exact_mod_cast hr) (by exact_mod_cast hi)

theorem norm_toK (u:O) : norm (toK u)=(u.norm:ℚ) := by
  rw [toK_pair,norm_pair]
  simp [Zsqrtd.norm_def,pow_two,mul_assoc]

theorem norm_nonzero {u:O} (hu:u≠0) : u.norm≠0 := by
  intro hh
  have hk:toK u≠0 := fun he=>hu (toK_injective (by simpa using he))
  exact norm_ne_zero hk (by rw [norm_toK,hh]; norm_num)

@[expose] def nearest (x:K) : O := ⟨round x.re,round x.im⟩

/-- Coefficientwise nearest-integer rounding gives absolute field norm
at most one half. This is the actual Euclidean approximation for sqrt2. -/
theorem nearest_norm_bound (x:K) : |norm (x-toK (nearest x))|≤(1/2:ℚ) := by
  have ha:=abs_sub_round x.re
  have hb:=abs_sub_round x.im
  have ha':=abs_le.mp ha
  have hb':=abs_le.mp hb
  have hqa:(x.re-(round x.re:ℚ))^2≤1/4 := by nlinarith
  have hqb:(x.im-(round x.im:ℚ))^2≤1/4 := by nlinarith
  have he:x-toK (nearest x)=pair (x.re-(round x.re:ℚ)) (x.im-(round x.im:ℚ)) := by
    ext <;> rfl
  rw [he,norm_pair,abs_le]
  constructor <;> nlinarith [sq_nonneg (x.re-(round x.re:ℚ)),sq_nonneg (x.im-(round x.im:ℚ))]

@[expose] def quotient (x y:O) : O := nearest (toK x/toK y)
@[expose] def remainder (x y:O) : O := x-y*quotient x y

theorem remainder_norm_lt (x y:O) (hy:y≠0) :
    (remainder x y).norm.natAbs<y.norm.natAbs := by
  have hk:toK y≠0 := fun he=>hy (toK_injective (by simpa using he))
  have hn:0 < |norm (toK y)| := abs_pos.mpr (norm_ne_zero hk)
  have he:toK (remainder x y)=toK y*(toK x/toK y-toK (nearest (toK x/toK y))) := by
    simp only [remainder,map_sub,map_mul,quotient]
    field_simp
  have hb:=nearest_norm_bound (toK x/toK y)
  have hh:|norm (toK (remainder x y))| < |norm (toK y)| := by
    rw [he,norm_mul,abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hb (le_of_lt hn)]
  rw [norm_toK,norm_toK] at hh
  rw [←Nat.cast_lt (α:=ℤ),Int.natCast_natAbs,Int.natCast_natAbs]
  exact_mod_cast hh

theorem norm_le_norm_mul (x y:O) (hy:y≠0) : x.norm.natAbs≤(x*y).norm.natAbs := by
  rw [Zsqrtd.norm_mul,Int.natAbs_mul]
  exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr (norm_nonzero hy))

/-- The actual integer order Z[sqrt2] is Euclidean for absolute norm. -/
noncomputable instance euclideanDomain : EuclideanDomain O :=
  { Zsqrtd.commRing, (inferInstance:Nontrivial O) with
    quotient:=quotient
    remainder:=remainder
    quotient_zero:=by intro x; ext <;> simp [quotient,nearest,toK]
    quotient_mul_add_remainder_eq:=by intro x y; simp [remainder]
    r:=fun x y=>x.norm.natAbs<y.norm.natAbs
    r_wellFounded:=(measure (fun x:O=>x.norm.natAbs)).wf
    remainder_lt:=remainder_norm_lt
    mul_left_not_lt:=fun x y hy=>not_lt_of_ge (norm_le_norm_mul x y hy) }

end
end EuclideanSqrtTwo318
#print axioms EuclideanSqrtTwo318.nearest_norm_bound
#print axioms EuclideanSqrtTwo318.euclideanDomain
