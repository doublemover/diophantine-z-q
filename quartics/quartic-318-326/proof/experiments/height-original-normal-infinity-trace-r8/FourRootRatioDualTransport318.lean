module
public import FourRootRatioGenericEquiv318
public import FourRootRatioDualCoefficient318
public import FiniteDualTransport318
public section
noncomputable section
namespace FourRootRatioDualTransport318
open FourRootRatioOrder318 FourRootRatioGenericEquiv318 FourRootOrderSigns318
open FourRootIntegralDuality318 FourRootRatioDualCoefficient318 FiniteDualTransport318
variable {R : Type*} [CommRing R] (q : R) (r : Fin 3 → R) (hq : IsUnit q)
local notation "A" => OriginalOrder q r
local notation "B" => RatioOrder q r
local notation "E" => equiv q r hq

/-- Entire finite-dual precomposition, with its correct order action,
proves the normalized generator is y0 cubed times the original generator. -/
lemma inverse_generator :
    transport E.symm (FiniteDualModuleAction318.frame R B (frame (normalized q r)) 1) =
      generator (original q r) 0^3 • FiniteDualModuleAction318.frame R A (frame (original q r)) 1 := by
  apply LinearMap.ext
  intro x
  change coefficient (normalized q r) (1*E x)=
    coefficient (original q r) (1*(generator (original q r) 0^3*x))
  simp only [one_mul]
  exact coefficient_map_cube q r x

/-- The full balanced tensor square consequently has discrepancy y0^6,
not a chosen scalar on a presentation of a pure tensor. -/
lemma inverse_square (x : B) :
    squareTransport E.symm (squareFrame (frame (normalized q r)) x)=
      squareFrame (frame (original q r)) (E.symm x*generator (original q r) 0^6) := by
  rw [squareTransport_frame E.symm (frame (normalized q r)) (frame (original q r)) _
    (inverse_generator q r hq)]
  congr 1
  ring

@[expose] def inverseCube : B := E ((↑(rootUnit q r hq)⁻¹ : A)^3)

lemma forward_generator :
    transport E (FiniteDualModuleAction318.frame R A (frame (original q r)) 1) =
      inverseCube q r hq • FiniteDualModuleAction318.frame R B (frame (normalized q r)) 1 := by
  apply LinearMap.ext
  intro x
  change coefficient (original q r) (1*E.symm x)=
    coefficient (normalized q r) (1*(inverseCube q r hq*x))
  simp only [one_mul]
  have he : inverseCube q r hq*x=E ((↑(rootUnit q r hq)⁻¹:A)^3*E.symm x) := by
    rw [map_mul,AlgEquiv.apply_symm_apply]
    rfl
  rw [he,coefficient_map_cube]
  congr 1
  rw [←rootUnit_value q r hq,←mul_assoc,←mul_pow,Units.mul_inv,one_pow,one_mul]

lemma forward_square (x : A) :
    squareTransport E (squareFrame (frame (original q r)) x)=
      squareFrame (frame (normalized q r)) (E x*E ((↑(rootUnit q r hq)⁻¹:A)^6)) := by
  rw [squareTransport_frame E (frame (original q r)) (frame (normalized q r)) _
    (forward_generator q r hq)]
  congr 1
  rw [inverseCube,←map_pow]
  congr 2
  ring

/-- Exact actual trace different comparison, using all four marked roots. -/
lemma different_map : E (16*∏ i : Fin 4,generator (original q r) i)=
    generator (normalized q r) 0^3*(16*∏ i : Fin 4,generator (normalized q r) i) := by
  simp only [map_mul,map_ofNat,map_prod,equiv_root,Fin.prod_univ_succ,Fin.prod_univ_zero,
    marked,Fin.cases_zero,Fin.cases_succ]
  ring
end FourRootRatioDualTransport318
