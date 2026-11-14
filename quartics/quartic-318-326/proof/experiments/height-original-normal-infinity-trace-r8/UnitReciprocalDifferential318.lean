module
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace UnitReciprocalDifferential318
open scoped TensorProduct
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (u : Aˣ)

theorem differential : KaehlerDifferential.D R A (↑u⁻¹ : A)=
    -((↑u⁻¹ : A)^2) • KaehlerDifferential.D R A (u : A) := by
  have h := congrArg (KaehlerDifferential.D R A) u.mul_inv
  simp only [Derivation.leibniz,Derivation.map_one_eq_zero] at h
  have hh := congrArg (fun z : KaehlerDifferential R A => (↑u⁻¹ : A) • z) h
  simp only [smul_add,smul_smul,Units.inv_mul,one_smul,smul_zero] at hh
  rw [neg_smul]
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [pow_two] using hh

theorem tensor_square :
    KaehlerDifferential.D R A (↑u⁻¹ : A) ⊗ₜ[A] KaehlerDifferential.D R A (↑u⁻¹ : A)=
      (↑u⁻¹ : A)^4 • (KaehlerDifferential.D R A (u : A) ⊗ₜ[A] KaehlerDifferential.D R A (u : A)) := by
  simp only [differential,TensorProduct.smul_tmul_smul]
  congr 1
  ring

theorem contact_product (a : Fin 4 → A) :
    (∏ i : Fin 4,((↑u⁻¹ : A)-a i))=
      (↑u⁻¹ : A)^4*(∏ i : Fin 4,(1-a i*(u : A))) := by
  have h (i : Fin 4) : (↑u⁻¹ : A)-a i=(↑u⁻¹ : A)*(1-a i*(u : A)) := by
    have hu : (↑u⁻¹ : A)*(u : A)=1 := u.inv_mul
    linear_combination a i*hu
  simp only [h,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
end UnitReciprocalDifferential318
