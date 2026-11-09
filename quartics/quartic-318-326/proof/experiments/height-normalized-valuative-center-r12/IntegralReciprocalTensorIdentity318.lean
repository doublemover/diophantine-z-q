module
public import IntrinsicTensorChartSections318
public import Mathlib.RingTheory.Kaehler.Basic
public section
noncomputable section
namespace IntegralReciprocalTensorIdentity318
open scoped TensorProduct
set_option maxHeartbeats 500000
variable {S : Type*} [CommRing S]

/-- Exact integral coefficient transport under y*u=c. Only the actual
coordinate and denominator inverses are used; no domain or field is assumed. -/
theorem coefficient_transport (c k y u v C F f D d : S)
    (hck : c*k=1) (hyu : y*u=c) (huv : u*v=1)
    (hF : F*f=1) (hD : D*d=1) (hFD : F=D*y^6) :
    (4*C*k*f)*(-(y*v))^2 = 4*C*k^5*u^2*d := by
  have hkyu : k*y*u=1 := by
    calc
      _ = k*(y*u) := by ring
      _ = 1 := by rw [hyu,mul_comm k c,hck]
  have hFu : IsUnit (F*u^2) :=
    (isUnit_iff_exists_inv.mpr ⟨f,hF⟩).mul
      ((isUnit_iff_exists_inv.mpr ⟨v,huv⟩).pow 2)
  apply hFu.mul_left_cancel
  calc
    (F*u^2)*((4*C*k*f)*(-(y*v))^2) =
        (4*C*k*y^2)*(F*f)*(u*v)^2 := by ring
    _ = 4*C*k*y^2 := by rw [hF,huv,one_pow,mul_one,mul_one]
    _ = (4*C*k*y^2)*(k*y*u)^4 := by rw [hkyu,one_pow,mul_one]
    _ = (4*C*k^5*u^4*y^6)*(D*d) := by rw [hD,mul_one];ring
    _ = (F*u^2)*(4*C*k^5*u^2*d) := by rw [hFD];ring

variable {R : Type*} [CommRing R] [Algebra R S]
/-- Differentiation of the actual overlap equation keeps the reciprocal
minus sign and coefficient. Cancellation is by the supplied inverse of u. -/
theorem D_reciprocal (y u v : S) (c : R)
    (hyu : y*u=algebraMap R S c) (huv : u*v=1) :
    KaehlerDifferential.D R S y = -(y*v) • KaehlerDifferential.D R S u := by
  have hd := congrArg (KaehlerDifferential.D R S) hyu
  simp only [Derivation.leibniz,Derivation.map_algebraMap] at hd
  have he : u • KaehlerDifferential.D R S y =
      -(y • KaehlerDifferential.D R S u) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_comm] using hd
  calc
    _ = (v*u) • KaehlerDifferential.D R S y := by rw [mul_comm v u,huv,one_smul]
    _ = v • (u • KaehlerDifferential.D R S y) := (smul_smul _ _ _).symm
    _ = v • (-(y • KaehlerDifferential.D R S u)) := by rw [he]
    _ = -(y*v) • KaehlerDifferential.D R S u := by module

/-- Equality of actual cotangent-square tensors, including arbitrary common
normalization such as the original J². -/
theorem tensor_agreement (A b d s : S) (ω η : KaehlerDifferential R S)
    (hω : ω=s • η) (hb : b*s^2=d) :
    (A*b) • (ω ⊗ₜ[S] ω) = (A*d) • (η ⊗ₜ[S] η) := by
  rw [hω,TensorProduct.smul_tmul_smul,smul_smul]
  have hs : (A*b)*(s*s)=A*d := by rw [←pow_two,mul_assoc,hb]
  rw [hs]
end IntegralReciprocalTensorIdentity318
