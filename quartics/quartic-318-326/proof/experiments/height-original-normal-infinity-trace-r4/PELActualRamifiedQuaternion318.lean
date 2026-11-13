module
public import PELPadicCoordinateAnisotropy318
public section
noncomputable section
namespace PELActualRamifiedQuaternion318
open PELPrimeNormalizerData318 PELRamifiedPrimitiveCongruence318
set_option maxHeartbeats 1800000

/-- The original quaternion presentation (-210,5) over the actual Q_p.
No unrelated quaternion algebra or local division input is supplied. -/
abbrev LocalAlgebra (i : Fin 4) := QuaternionAlgebra ℚ_[prime i] (-210) 0 5
@[expose] def localNorm (i : Fin 4) (x : LocalAlgebra i) : ℚ_[prime i] :=
  x.re^2+210*x.imI^2-5*x.imJ^2-1050*x.imK^2
@[expose] def coordinates (i : Fin 4) (x : LocalAlgebra i) : Fin 4 → ℚ_[prime i] :=
  ![x.re-x.imJ,x.imI-5*x.imK,2*x.imJ,10*x.imK]

theorem coordinate_norm (i : Fin 4) (x : LocalAlgebra i) :
    polynomial (coordinates i x)=localNorm i x := by
  simp [coordinates,polynomial,localNorm]
  ring

theorem coordinates_ne_zero (i : Fin 4) (x : LocalAlgebra i) (hx : x≠0) : coordinates i x≠0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [coordinates,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Pi.zero_apply] at h0 h1 h2 h3
  apply hx
  ext
  · change x.re=0
    linear_combination h0+(1/2:ℚ_[prime i])*h2
  · change x.imI=0
    linear_combination h1+(1/2:ℚ_[prime i])*h3
  · change x.imJ=0
    linear_combination (1/2:ℚ_[prime i])*h2
  · change x.imK=0
    linear_combination (1/10:ℚ_[prime i])*h3

theorem localNorm_ne_zero (i : Fin 4) (x : LocalAlgebra i) (hx : x≠0) : localNorm i x≠0 := by
  rw [←coordinate_norm]
  exact PELPadicCoordinateAnisotropy318.anisotropic i _ (coordinates_ne_zero i x hx)

@[expose] def reciprocal (i : Fin 4) (x : LocalAlgebra i) : LocalAlgebra i :=
  (localNorm i x)⁻¹ • star x

theorem norm_identity (i : Fin 4) (x : LocalAlgebra i) :
    x*star x=algebraMap ℚ_[prime i] (LocalAlgebra i) (localNorm i x) := by
  ext <;> simp [localNorm,QuaternionAlgebra.algebraMap_eq] <;> ring

theorem norm_identity_left (i : Fin 4) (x : LocalAlgebra i) :
    star x*x=algebraMap ℚ_[prime i] (LocalAlgebra i) (localNorm i x) := by
  ext <;> simp [localNorm,QuaternionAlgebra.algebraMap_eq] <;> ring

theorem mul_reciprocal (i : Fin 4) (x : LocalAlgebra i) (hx : x≠0) : x*reciprocal i x=1 := by
  have hn := localNorm_ne_zero i x hx
  calc
    x*reciprocal i x=(localNorm i x)⁻¹ • (x*star x) := mul_smul_comm _ _ _
    _ = (localNorm i x)⁻¹ • algebraMap ℚ_[prime i] (LocalAlgebra i) (localNorm i x) := by rw [norm_identity]
    _ = 1 := by rw [Algebra.smul_def,←map_mul,inv_mul_cancel₀ hn,map_one]

theorem reciprocal_mul (i : Fin 4) (x : LocalAlgebra i) (hx : x≠0) : reciprocal i x*x=1 := by
  have hn := localNorm_ne_zero i x hx
  calc
    reciprocal i x*x=(localNorm i x)⁻¹ • (star x*x) := smul_mul_assoc _ _ _
    _ = (localNorm i x)⁻¹ • algebraMap ℚ_[prime i] (LocalAlgebra i) (localNorm i x) := by rw [norm_identity_left]
    _ = 1 := by rw [Algebra.smul_def,←map_mul,inv_mul_cancel₀ hn,map_one]

/-- Actual local division at all four ramified primes: every nonzero
original local quaternion has its displayed two-sided inverse. -/
theorem every_nonzero_isUnit (i : Fin 4) (x : LocalAlgebra i) (hx : x≠0) : IsUnit x :=
  ⟨⟨x,reciprocal i x,mul_reciprocal i x hx,reciprocal_mul i x hx⟩,rfl⟩

/-- The original rational quaternion algebra maps coefficientwise into this
specific local presentation, preserving the original parameters and norm. -/
@[expose] def rationalMap (i : Fin 4) : PELQuaternionAlgebra318.B →+* LocalAlgebra i where
  toFun x := ⟨(x.re:ℚ_[prime i]),(x.imI:ℚ_[prime i]),(x.imJ:ℚ_[prime i]),(x.imK:ℚ_[prime i])⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> push_cast <;> norm_num <;> ring

theorem rationalMap_norm (i : Fin 4) (x : PELQuaternionAlgebra318.B) :
    localNorm i (rationalMap i x)=(PELQuaternionAlgebra318.reducedNorm x:ℚ_[prime i]) := by
  simp [rationalMap,localNorm,PELQuaternionAlgebra318.reducedNorm] <;> push_cast <;> ring

theorem rationalMap_injective (i : Fin 4) : Function.Injective (rationalMap i) := by
  intro x y h
  have hr := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  change (x.re:ℚ_[prime i])=(y.re:ℚ_[prime i]) at hr
  change (x.imI:ℚ_[prime i])=(y.imI:ℚ_[prime i]) at hi
  change (x.imJ:ℚ_[prime i])=(y.imJ:ℚ_[prime i]) at hj
  change (x.imK:ℚ_[prime i])=(y.imK:ℚ_[prime i]) at hk
  ext
  · exact_mod_cast hr
  · exact_mod_cast hi
  · exact_mod_cast hj
  · exact_mod_cast hk
end PELActualRamifiedQuaternion318
