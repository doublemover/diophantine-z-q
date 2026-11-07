module
public import UnitDifferential318
public section
noncomputable section
namespace ShortInfinityDifferential318
set_option maxHeartbeats 200000
variable {R T M : Type*} [CommRing R] [CommRing T] [AddCommGroup M]
  [Algebra R T] [Module T M] [Module R M] [IsScalarTower R T M]

@[expose] def jacobian (a b x z : T) : T := 1-2*a*x*z-3*b*z^2
@[expose] def otherPartial (a x z : T) : T := 3*x^2+a*z^2

/-- The actual universal derivative of the infinity equation. -/
theorem differentiated_relation (d : Derivation R T M) (a b x z : T)
    (ha : d a=0) (hb : d b=0) (hF : z-x^3-a*x*z^2-b*z^3=0) :
    jacobian a b x z • d z = otherPartial a x z • d x := by
  have h := congrArg d hF
  simp only [map_sub,d.leibniz,d.leibniz_pow,ha,hb,smul_zero,add_zero,zero_add,map_zero] at h
  norm_num at h
  dsimp [jacobian,otherPartial]
  linear_combination (norm := module) h

/-- A literal polynomial identity, retaining the infinity equation and its sign. -/
theorem scalar_identity (a b x z : T) (hF : z-x^3-a*x*z^2-b*z^3=0) :
    z*jacobian a b x z-x*otherPartial a x z = -2*z := by
  dsimp [jacobian,otherPartial]
  linear_combination 3*hF

theorem reciprocal_scalar_identity (a b x z v : T)
    (hF : z-x^3-a*x*z^2-b*z^3=0) (hzv : z*v=1) :
    v*jacobian a b x z-x*v^2*otherPartial a x z = -2*v := by
  have h := scalar_identity a b x z hF
  calc
    _ = v^2*(z*jacobian a b x z-x*otherPartial a x z)+
        v*jacobian a b x z*(1-z*v) := by ring
    _ = -2*v := by rw [h,hzv]; linear_combination (-2*v)*hzv

/-- The actual overlap identity has a minus sign, with no field-division operation. -/
theorem invariant_cross_identity (d : Derivation R T M) (a b x z v : T)
    (ha : d a=0) (hb : d b=0) (hF : z-x^3-a*x*z^2-b*z^3=0) (hzv : z*v=1) :
    jacobian a b x z • d (x*v) = -(2*v) • d x := by
  rw [UnitDifferential318.ratio d x z v hzv]
  calc
    _ = v • (jacobian a b x z • d x) -
        (x*v^2) • (jacobian a b x z • d z) := by module
    _ = v • (jacobian a b x z • d x) -
        (x*v^2) • (otherPartial a x z • d x) := by rw [differentiated_relation d a b x z ha hb hF]
    _ = (v*jacobian a b x z-x*v^2*otherPartial a x z) • d x := by module
    _ = -(2*v) • d x := by rw [reciprocal_scalar_identity a b x z v hF hzv]; congr 1; ring

/-- After the two actual denominators are inverted, the invariant differentials agree. -/
theorem invariant_form_identity (d : Derivation R T M) (a b x z v : T)
    (ha : d a=0) (hb : d b=0) (hF : z-x^3-a*x*z^2-b*z^3=0) (hzv : z*v=1)
    (jinv finv : T) (hj : jacobian a b x z*jinv=1) (hf : (2*v)*finv=1) :
    finv • d (x*v) = -jinv • d x := by
  have h := congrArg (fun m:M => (jinv*finv) • m) (invariant_cross_identity d a b x z v ha hb hF hzv)
  have hj' : (jinv*finv)*jacobian a b x z=finv := by
    calc
      _ = finv*(jacobian a b x z*jinv) := by ring
      _ = finv := by rw [hj,mul_one]
  have hf' : (jinv*finv)*(-(2*v)) = -jinv := by
    calc
      _ = -jinv*((2*v)*finv) := by ring
      _ = -jinv := by rw [hf,mul_one]
  simpa only [smul_smul,hj',hf'] using h

end ShortInfinityDifferential318
