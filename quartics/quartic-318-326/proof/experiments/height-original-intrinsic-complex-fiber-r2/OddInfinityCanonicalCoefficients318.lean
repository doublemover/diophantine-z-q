module
public import OddInfinityWholeModelMap318
public import NormalizedDualBicanonicalSections318
public section
noncomputable section
namespace OddInfinityCanonicalCoefficients318
open Polynomial ThreePolynomialEtaleChart318 OddInfinitySmoothChart318 OddInfinityWholeModelMap318
variable (V : Type*) [CommRing V] (pi : V) (u : Fin 4 → Vˣ) (d a : Fin 4 → V)
local notation "Q" => OddInfinitySmoothChart318.coefficient V pi u a
local notation "C" => ModelRing V pi u a

lemma ratio_unit (j : Fin 3) : IsUnit (ratio V pi u a j) := by
  apply (isUnit_pow_iff (by decide : (2:ℕ)≠0)).mp
  rw [ratio_square_polynomial]
  exact (coefficient_unit V Q j).map (algebraMap (Base V Q) C)
@[expose] def ratioProductUnit : Cˣ :=
  (IsUnit.prod_univ_iff.mpr (fun j => ratio_unit V pi u a j)).unit
lemma ratioProductUnit_value : (ratioProductUnit V pi u a:C)=∏j:Fin 3,ratio V pi u a j :=
  (IsUnit.prod_univ_iff.mpr (fun j => ratio_unit V pi u a j)).unit_spec

@[expose] def different : C := 16*∏i:Fin 4,signedRoot V pi u a i
@[expose] def derivative : C := algebraMap V C (2*pi*(↑(u 0)⁻¹:V))*z V pi u a
/-- Actual integral canonical coefficient. Its inverse factors are only
units already PRODUCED on the smooth chart; pi is not inverted. -/
@[expose] def coefficient1 : C :=
  algebraMap V C (4*pi*(∏i:Fin 4,(u i:V))*(↑(u 0)⁻¹:V)^5)*
    (↑(ratioProductUnit V pi u a)⁻¹:C)^2
@[expose] def coefficient0 : C := coefficient1 V pi u a*s V pi u a

lemma different_eq : different V pi u a=
    16*(algebraMap V C pi)^4*(z V pi u a)^4*(ratioProductUnit V pi u a:C) := by
  rw [different,ratioProductUnit_value]
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,signedRoot,Fin.cases_zero,Fin.cases_succ]
  ring

/-- Universal cancellation identity over a commutative ring. All inverse
powers are powers of the specified genuine unit. -/
lemma cancellation {A : Type*} [CommRing A] (p z U v : A) (r : Aˣ) :
    (4*p*U*v^5*(↑r⁻¹:A)^2)*(16*p^4*z^4*(r:A))^2=
      (256*p^4*U)*(p*v*z^2)^3*(2*p*v*z)^2 := by
  calc
    _ = (1024*p^9*U*v^5*z^8)*((↑r⁻¹:A)*(r:A))^2 := by ring
    _ = _ := by rw [Units.inv_mul,one_pow,mul_one]; ring

variable (hd : ∀ i,d i=(u i:V)*pi)
include hd in
lemma twist_product : (∏i:Fin 4,d i)=pi^4*∏i:Fin 4,(u i:V) := by
  simp only [hd,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

include hd in
lemma coefficient1_identity : coefficient1 V pi u a*(different V pi u a)^2=
    algebraMap V C (NormalizedDualBicanonicalSections318.sectionCoefficient V d)*
      (s V pi u a)^3*(derivative V pi u a)^2 := by
  rw [coefficient1,different_eq,NormalizedDualBicanonicalSections318.sectionCoefficient,
    twist_product V pi u d hd,s_eq,derivative]
  simp only [map_mul,map_pow,map_ofNat]
  convert cancellation (algebraMap V C pi) (z V pi u a)
    (algebraMap V C (∏i:Fin 4,(u i:V))) (algebraMap V C (↑(u 0)⁻¹:V))
    (ratioProductUnit V pi u a) using 1 <;> ring

include hd in
lemma coefficient0_identity : coefficient0 V pi u a*(different V pi u a)^2=
    algebraMap V C (NormalizedDualBicanonicalSections318.sectionCoefficient V d)*
      (s V pi u a)^4*(derivative V pi u a)^2 := by
  rw [coefficient0]
  calc
    _ = (coefficient1 V pi u a*(different V pi u a)^2)*s V pi u a := by ring
    _ = _ := by rw [coefficient1_identity V pi u d a hd]; ring

/-- Actual universal differential identity in the entire smooth chart,
proved using its produced Kaehler frame. -/
lemma D_reciprocal (h2 : IsUnit (2:V)) :
    KaehlerDifferential.D V C (s V pi u a)=
      derivative V pi u a • KaehlerDifferential.D V C (z V pi u a) := by
  apply (ThreePolynomialEtaleChart318.frame V Q h2).injective
  rw [map_smul,show z V pi u a=coordinate V Q from rfl,coordinate_normalized,smul_eq_mul,mul_one]
  change ThreePolynomialEtaleChart318.frame V Q h2
    (KaehlerDifferential.D V C (reciprocalValue V pi u a))=_
  rw [OddInfinitySmoothChart318.frame_reciprocal]
  have hp : (reciprocal V pi u).derivative=Polynomial.C (2*pi*(↑(u 0)⁻¹:V))*X := by
    simp only [reciprocal,Polynomial.derivative_mul,Polynomial.derivative_C,
      zero_mul,zero_add,Polynomial.derivative_pow,Polynomial.derivative_X]
    ring
  rw [hp]
  change algebraMap (Base V Q) C (algebraMap V[X] (Base V Q)
    (Polynomial.C (2*pi*(↑(u 0)⁻¹:V))*X))=_
  rw [map_mul,map_mul]
  rw [show algebraMap (Base V Q) C
    (algebraMap V[X] (Base V Q) (Polynomial.C (2*pi*(↑(u 0)⁻¹:V))))=_ from
      polynomial_C V pi u a _]
  rfl
end OddInfinityCanonicalCoefficients318
