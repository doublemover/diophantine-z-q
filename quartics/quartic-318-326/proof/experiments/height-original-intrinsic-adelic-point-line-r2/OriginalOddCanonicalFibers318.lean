module
public import OriginalCommonOddCanonicalExtension318
public import FramedDifferentialTensorFiber318
public section
noncomputable section
namespace OriginalOddCanonicalFibers318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OddInfinityWholeModelMap318 OddInfinityCanonicalCoefficients318
open OriginalOddCanonicalCenter318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
  (P : OriginalOddReciprocalCenter318.Center c t w D)
local notation "V" => OriginalPointFinitePlaceRoots318.V c t w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "C" => OriginalOddReciprocalCenter318.Ring c t w D
local notation "Q" => OriginalOddReciprocalCenter318.coefficients c t w D
local notation "e" => OriginalOddReciprocalCenter318.point c t w D P
@[expose] def b0 : V := (ContactScaledBicanonicalPoint318.J:V)^2*e (coefficient0 V D.pi D.unit a)
@[expose] def b1 : V := (ContactScaledBicanonicalPoint318.J:V)^2*e (coefficient1 V D.pi D.unit a)

variable (h2 : IsUnit (2:V))
@[expose] def tensorFiber :
    (KaehlerDifferential V C ⊗[C] KaehlerDifferential V C) →ₛₗ[e] V :=
  FramedDifferentialTensorFiber318.tensorFiber e (ThreePolynomialEtaleChart318.frame V Q h2)
lemma tensor_fiber0 : tensorFiber c t w D P h2 (ContactScaledBicanonicalPoint318.J^2 •
    OddInfinityIntegralCanonicalTensors318.integral0 V D.pi D.unit a)=b0 c t w D P := by
  rw [map_nsmul]
  change ContactScaledBicanonicalPoint318.J^2 •
    FramedDifferentialTensorFiber318.tensorFiber e (ThreePolynomialEtaleChart318.frame V Q h2)
      (coefficient0 V D.pi D.unit a •
        (KaehlerDifferential.D V C (z V D.pi D.unit a) ⊗ₜ[C]
          KaehlerDifferential.D V C (z V D.pi D.unit a)))=_
  rw [FramedDifferentialTensorFiber318.tensorFiber_weighted _ _ _ _
    (ThreePolynomialEtaleChart318.coordinate_normalized V Q h2)]
  simp only [b0,nsmul_eq_mul,Nat.cast_pow]
lemma tensor_fiber1 : tensorFiber c t w D P h2 (ContactScaledBicanonicalPoint318.J^2 •
    OddInfinityIntegralCanonicalTensors318.integral1 V D.pi D.unit a)=b1 c t w D P := by
  rw [map_nsmul]
  change ContactScaledBicanonicalPoint318.J^2 •
    FramedDifferentialTensorFiber318.tensorFiber e (ThreePolynomialEtaleChart318.frame V Q h2)
      (coefficient1 V D.pi D.unit a •
        (KaehlerDifferential.D V C (z V D.pi D.unit a) ⊗ₜ[C]
          KaehlerDifferential.D V C (z V D.pi D.unit a)))=_
  rw [FramedDifferentialTensorFiber318.tensorFiber_weighted _ _ _ _
    (ThreePolynomialEtaleChart318.coordinate_normalized V Q h2)]
  simp only [b1,nsmul_eq_mul,Nat.cast_pow]

lemma coefficient1_ne : e (coefficient1 V D.pi D.unit a)≠0 := by
  rw [coefficient1,map_mul,OriginalOddReciprocalCenter318.point_scalar,map_pow]
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) D.irreducible.ne_zero)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => (D.unit i).ne_zero)))
      (pow_ne_zero _ ((D.unit 0)⁻¹).ne_zero)
  · exact pow_ne_zero _ (((ratioProductUnit V D.pi D.unit a)⁻¹).isUnit.map e).ne_zero
lemma reciprocal_ne : reciprocalCoordinate c t w D P≠0 := by
  change Polynomial.eval P.coordinate (Polynomial.C (D.pi*(↑(D.unit 0)⁻¹:V))*Polynomial.X^2)≠0
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  exact mul_ne_zero (mul_ne_zero D.irreducible.ne_zero ((D.unit 0)⁻¹).ne_zero)
    (pow_ne_zero _ P.coordinate_ne)
lemma b0_ne : b0 c t w D P≠0 := by
  rw [b0,coefficient0,map_mul,point_s]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num [ContactScaledBicanonicalPoint318.J]))
    (mul_ne_zero (coefficient1_ne c t w D P) (reciprocal_ne c t w D P))
lemma ratio : algebraMap V (K c t) (b1 c t w D P)=
    (t:K c t)*algebraMap V (K c t) (b0 c t w D P) := by
  have h : b0 c t w D P=b1 c t w D P*reciprocalCoordinate c t w D P := by
    rw [b0,b1,coefficient0,map_mul,point_s]
    ring
  have hn : (t:K c t)⁻¹≠0 := by
    rw [←P.reciprocal]
    simpa only [map_zero] using (IsFractionRing.injective V (K c t)).ne (reciprocal_ne c t w D P)
  rw [h,map_mul,P.reciprocal]
  field_simp [inv_ne_zero_iff.mp hn]

/-- Finite bounds are values of the actual canonical tensor fibers at
this integral smooth center, not bounds assigned to an arbitrary frame. -/
lemma finite_bounds : w (algebraMap V (K c t) (b0 c t w D P))≤1 ∧
    w (algebraMap V (K c t) (b1 c t w D P))≤1 :=
  ⟨ActualFinitePlaceIntegers318.integer_bound w _,ActualFinitePlaceIntegers318.integer_bound w _⟩
end OriginalOddCanonicalFibers318
