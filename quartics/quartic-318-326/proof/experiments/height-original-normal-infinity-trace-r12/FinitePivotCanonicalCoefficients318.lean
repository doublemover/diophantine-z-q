module
public import FinitePivotCanonicalSource318
public import NormalizedDualBicanonicalSections318
public section
noncomputable section
namespace FinitePivotCanonicalCoefficients318
open Polynomial OddTwistDilatationEtale318 FinitePivotCanonicalSource318
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (rho : V) (u : Vˣ) (d a : Fin 4 → V) (i : Fin 4)
local notation "C" => FinitePivotCanonicalSource318.Chart V rho u d a i
local notation "B" => OddTwistDilatationEtale318.Base V rho u (a i) (others V d i) (others V a i)
@[expose] def z : C := coordinate V rho u (a i) (others V d i) (others V a i)
@[expose] def t : C := contactValue V rho u (a i) (others V d i) (others V a i)
@[expose] def root (j : Fin 3) : C := ThreeRootCoordinates318.generator _ j
lemma root_unit (j : Fin 3) : IsUnit (root V rho u d a i j) := by
  apply (isUnit_pow_iff (by decide : (2:ℕ)≠0)).mp
  rw [show (root V rho u d a i j)^2=_ from
    OddTwistDilatationSourceMap318.three_root_square V rho u (a i) (others V d i) (others V a i) j]
  exact (coefficient_unit V rho u (a i) (others V d i) (others V a i) j).map (algebraMap B C)
@[expose] def productUnit : Cˣ := (IsUnit.prod_univ_iff.mpr (fun j => root_unit V rho u d a i j)).unit
lemma productUnit_value : (productUnit V rho u d a i:C)=∏j:Fin 3,root V rho u d a i j :=
  (IsUnit.prod_univ_iff.mpr (fun j => root_unit V rho u d a i j)).unit_spec
@[expose] def different : C := 16*∏k:Fin 4,originalRoot V rho u d a i k
@[expose] def derivative : C := 2*algebraMap V C (rho*(↑u⁻¹:V))*z V rho u d a i
@[expose] def coefficient0 : C := algebraMap V C
  (4*rho*(↑u⁻¹:V)*(∏j:Fin 3,d (FourRootPivot318.indices i j.succ)))*(↑(productUnit V rho u d a i)⁻¹:C)^2
@[expose] def coefficient1 : C := t V rho u d a i*coefficient0 V rho u d a i

lemma different_eq : different V rho u d a i=
    16*algebraMap V C rho*z V rho u d a i*(productUnit V rho u d a i:C) := by
  rw [different,productUnit_value]
  have hprod := (indexEquiv i).prod_comp (originalRoot V rho u d a i)
  rw [←hprod]
  simp only [originalRoot_index,Fin.prod_univ_succ,Fin.prod_univ_zero,
    OddTwistDilatationSourceMap318.originalRoot,Fin.cases_zero,Fin.cases_succ,one_mul,mul_one,root,z]
  ring

lemma cancellation {A : Type*} [CommRing A] (p Z D : A) (u : Aˣ) (r : Aˣ) :
    (4*p*(↑u⁻¹:A)*D*(↑r⁻¹:A)^2)*(16*p*Z*(r:A))^2=
      (256*((u:A)*p)*D)*(2*(p*(↑u⁻¹:A))*Z)^2 := by
  have hu : (u:A)*(↑u⁻¹:A)=1 := Units.mul_inv _
  have hr : (↑r⁻¹:A)*(r:A)=1 := Units.inv_mul _
  calc
    _ = 1024*p^3*Z^2*(↑u⁻¹:A)*D*((↑r⁻¹:A)*(r:A))^2 := by ring
    _ = 1024*p^3*Z^2*(↑u⁻¹:A)*D := by rw [hr,one_pow,mul_one]
    _ = 1024*p^3*Z^2*(↑u⁻¹:A)*D*((u:A)*(↑u⁻¹:A)) := by rw [hu,mul_one]
    _ = _ := by ring

variable (hd : d i=(u:V)*rho)
include hd in
lemma coefficient0_identity : coefficient0 V rho u d a i*(different V rho u d a i)^2=
    algebraMap V C (NormalizedDualBicanonicalSections318.sectionCoefficient V d)*
      (derivative V rho u d a i)^2 := by
  rw [coefficient0,different_eq,NormalizedDualBicanonicalSections318.sectionCoefficient,
    product_pivot V i d,hd,derivative]
  simp only [map_mul,map_ofNat]
  convert cancellation (algebraMap V C rho) (z V rho u d a i)
    (algebraMap V C (∏j:Fin 3,d (FourRootPivot318.indices i j.succ)))
    (Units.map (algebraMap V C) u) (productUnit V rho u d a i) using 1 <;> simp only [Units.coe_map,Units.coe_map_inv] <;> ring
include hd in
lemma coefficient1_identity : coefficient1 V rho u d a i*(different V rho u d a i)^2=
    (t V rho u d a i*algebraMap V C (NormalizedDualBicanonicalSections318.sectionCoefficient V d))*
      (derivative V rho u d a i)^2 := by
  rw [coefficient1]
  calc
    _ = t V rho u d a i*(coefficient0 V rho u d a i*(different V rho u d a i)^2) := by ring
    _ = _ := by rw [coefficient0_identity V rho u d a i hd]; ring

lemma D_contact (h2 : IsUnit (2:V)) : KaehlerDifferential.D V C (t V rho u d a i)=
    derivative V rho u d a i • KaehlerDifferential.D V C (z V rho u d a i) := by
  apply (OddTwistDilatationEtale318.frame V rho u (a i) (others V d i) (others V a i) h2).injective
  rw [map_smul,show z V rho u d a i=coordinate V rho u (a i) (others V d i) (others V a i) from rfl,
    coordinate_normalized,smul_eq_mul,mul_one]
  exact frame_D_contact V rho u (a i) (others V d i) (others V a i) h2
end FinitePivotCanonicalCoefficients318
