module
public import CompletedRationalNormal318
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
namespace BivariateIntegral318
open Polynomial
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Base:=Polynomial ℚ
/-- Full quotient integrality follows from its two actual coordinate
classes, not just from integrality of an affine presentation's names. -/
theorem quotient_integral (I:Ideal (MvPolynomial (Fin 2) ℚ))
    [Algebra Base (MvPolynomial (Fin 2) ℚ⧸I)]
    [IsScalarTower ℚ Base (MvPolynomial (Fin 2) ℚ⧸I)]
    (h:∀i:Fin 2,IsIntegral Base (Ideal.Quotient.mk I (MvPolynomial.X i))):
    Algebra.IsIntegral Base (MvPolynomial (Fin 2) ℚ⧸I):=by
  constructor
  intro x
  obtain ⟨f,rfl⟩:=Ideal.Quotient.mk_surjective x
  induction f using MvPolynomial.induction_on with
  | C a=>
    change IsIntegral Base (algebraMap ℚ (MvPolynomial (Fin 2) ℚ⧸I) a)
    rw [IsScalarTower.algebraMap_apply ℚ Base (MvPolynomial (Fin 2) ℚ⧸I)]
    exact isIntegral_algebraMap
  | add f g hf hg=>simpa only [map_add] using hf.add hg
  | mul_X f i hf=>simpa only [map_mul] using hf.mul (h i)
lemma monic_cubic {R:Type*} [CommRing R] (a b:R):
    (X^3+C a*X+C b:Polynomial R).Monic:=by
  rw [add_assoc]
  apply Polynomial.monic_X_pow_add
  calc
    (C a*X+C b:Polynomial R).degree≤1:=
      Polynomial.degree_add_le_of_degree_le (Polynomial.degree_C_mul_X_le a)
        (Polynomial.degree_C_le.trans (by norm_num))
    _ < (3:ℕ):=by norm_num
/-- The needed flatness criterion retains actual injectivity, rather than
inferring it from a finite map or a generic degree statement. -/
theorem flat_of_injective {R S:Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDomain S] [Algebra R S]
    (h:Function.Injective (algebraMap R S)):Module.Flat R S:=by
  letI:Module.IsTorsionFree R S:=Module.isTorsionFree_iff_algebraMap_injective.mpr h
  infer_instance
end BivariateIntegral318
