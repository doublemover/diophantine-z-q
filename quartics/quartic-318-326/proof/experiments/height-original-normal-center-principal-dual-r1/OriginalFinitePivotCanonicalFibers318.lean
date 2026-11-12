module
public import OriginalFinitePivotCanonicalExtension318
public import FramedDifferentialTensorFiber318
public section
noncomputable section
namespace OriginalFinitePivotCanonicalFibers318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open FinitePivotCanonicalSource318 FinitePivotCanonicalCoefficients318 OriginalFinitePivotCanonicalCenter318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (tau : ℚ) (w : FinitePlace (K c tau)) (D : Data c tau w) (i : Fin 4)
  (P : Center c tau w D i)
local notation "V" => OriginalPointFinitePlaceRoots318.V c tau w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "d" => D.coefficients
local notation "C" => FinitePivotCanonicalSource318.Chart V D.pi (D.unit i) d a i
local notation "e" => point c tau w D i P
@[expose] def b0 : V := (ContactScaledBicanonicalPoint318.J:V)^2*e (coefficient0 V D.pi (D.unit i) d a i)
@[expose] def b1 : V := (ContactScaledBicanonicalPoint318.J:V)^2*e (coefficient1 V D.pi (D.unit i) d a i)
variable (h2 : IsUnit (2:V))
@[expose] def tensorFiber : (KaehlerDifferential V C ⊗[C] KaehlerDifferential V C) →ₛₗ[e] V :=
  FramedDifferentialTensorFiber318.tensorFiber e
    (OddTwistDilatationEtale318.frame V D.pi (D.unit i) (a i) (others V d i) (others V a i) h2)
lemma tensor_fiber0 : tensorFiber c tau w D i P h2 (ContactScaledBicanonicalPoint318.J^2 •
    FinitePivotIntegralCanonicalTensors318.integral0 V D.pi (D.unit i) d a i)=b0 c tau w D i P := by
  rw [map_nsmul]
  change ContactScaledBicanonicalPoint318.J^2 • FramedDifferentialTensorFiber318.tensorFiber e
    (OddTwistDilatationEtale318.frame V D.pi (D.unit i) (a i) (others V d i) (others V a i) h2)
    (coefficient0 V D.pi (D.unit i) d a i •
      (KaehlerDifferential.D V C (z V D.pi (D.unit i) d a i) ⊗ₜ[C]
        KaehlerDifferential.D V C (z V D.pi (D.unit i) d a i)))=_
  rw [FramedDifferentialTensorFiber318.tensorFiber_weighted _ _ _ _
    (OddTwistDilatationEtale318.coordinate_normalized V D.pi (D.unit i) (a i)
      (others V d i) (others V a i) h2)]
  simp only [b0,nsmul_eq_mul,Nat.cast_pow]
lemma tensor_fiber1 : tensorFiber c tau w D i P h2 (ContactScaledBicanonicalPoint318.J^2 •
    FinitePivotIntegralCanonicalTensors318.integral1 V D.pi (D.unit i) d a i)=b1 c tau w D i P := by
  rw [map_nsmul]
  change ContactScaledBicanonicalPoint318.J^2 • FramedDifferentialTensorFiber318.tensorFiber e
    (OddTwistDilatationEtale318.frame V D.pi (D.unit i) (a i) (others V d i) (others V a i) h2)
    (coefficient1 V D.pi (D.unit i) d a i •
      (KaehlerDifferential.D V C (z V D.pi (D.unit i) d a i) ⊗ₜ[C]
        KaehlerDifferential.D V C (z V D.pi (D.unit i) d a i)))=_
  rw [FramedDifferentialTensorFiber318.tensorFiber_weighted _ _ _ _
    (OddTwistDilatationEtale318.coordinate_normalized V D.pi (D.unit i) (a i)
      (others V d i) (others V a i) h2)]
  simp only [b1,nsmul_eq_mul,Nat.cast_pow]

lemma coefficient0_ne : e (coefficient0 V D.pi (D.unit i) d a i)≠0 := by
  have hd (k : Fin 4) : d k≠0 :=
    mul_ne_zero (D.unit k).ne_zero (pow_ne_zero _ D.irreducible.ne_zero)
  rw [coefficient0,map_mul,point_scalar,map_pow]
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) D.irreducible.ne_zero)
      ((D.unit i)⁻¹).ne_zero) (Finset.prod_ne_zero_iff.mpr (fun j _ => hd _))
  · exact pow_ne_zero _ (((productUnit V D.pi (D.unit i) d a i)⁻¹).isUnit.map e).ne_zero
lemma b0_ne : b0 c tau w D i P≠0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num [ContactScaledBicanonicalPoint318.J]))
    (coefficient0_ne c tau w D i P)
lemma field_ratio : algebraMap V (K c tau) (b1 c tau w D i P)=
    (tau:K c tau)*algebraMap V (K c tau) (b0 c tau w D i P) := by
  have h : b1 c tau w D i P=e (t V D.pi (D.unit i) d a i)*b0 c tau w D i P := by
    rw [b1,b0,coefficient1,map_mul]
    ring
  rw [h,map_mul]
  have ht : e (t V D.pi (D.unit i) d a i)=Polynomial.eval P.coordinate
      (OddTwistDilatationCoordinates318.contact D.pi (D.unit i) (a i)) :=
    OddTwistDilatationEtale318.point_contact _ _ _ _ _ _ _ _ _ _
  rw [ht,P.contact]
lemma finite_bounds : w (algebraMap V (K c tau) (b0 c tau w D i P))≤1 ∧
    w (algebraMap V (K c tau) (b1 c tau w D i P))≤1 :=
  ⟨ActualFinitePlaceIntegers318.integer_bound w _,ActualFinitePlaceIntegers318.integer_bound w _⟩
end OriginalFinitePivotCanonicalFibers318
