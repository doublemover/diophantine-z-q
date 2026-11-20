module
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public section
noncomputable section
open Polynomial KaehlerDifferential
open scoped TensorProduct

namespace SelectedMonogenicCotangentDivisibility318

section Monogenic
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- The conormal exact sequence for the actual integral monogenic
presentation. If c kills the differential of this very coordinate,
c is a multiple of its actual equation derivative in B, not just in
the generic splitting algebra. Surjectivity and kernel matter. -/
theorem derivative_dvd_of_kills_dx (α : R[X] →ₐ[R] B)
    (surj : Function.Surjective α) (p : R[X]) (hp : α p = 0)
    (kernel : ∀ q : R[X], α q = 0 → p ∣ q)
    (c : B) (kill : c • D R B (α X) = 0) :
    ∃ w : B, α p.derivative * w = c := by
  letI : Algebra R[X] B := α.toRingHom.toAlgebra
  letI : IsScalarTower R R[X] B := IsScalarTower.of_algHom α
  letI : SMulCommClass B R[X] B := SMulCommClass.of_commMonoid B R[X] B
  let x : B ⊗[R[X]] KaehlerDifferential R R[X] := c ⊗ₜ[R[X]] D R R[X] X
  have hx : mapBaseChange R R[X] B x = 0 := by
    dsimp only [x]
    rw [mapBaseChange_tmul,map_D]
    exact kill
  obtain ⟨k,hk⟩ :=
    (exact_kerCotangentToTensor_mapBaseChange R R[X] B surj x).mp hx
  obtain ⟨f,rfl⟩ := Ideal.toCotangent_surjective _ k
  have hdiv : p ∣ f.1 := kernel f.1 (RingHom.mem_ker.mp f.2)
  obtain ⟨q,hq⟩ := hdiv
  let E : (B ⊗[R[X]] KaehlerDifferential R R[X]) ≃ₗ[B] B :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) (polynomialEquiv R) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid R[X] B B
  have hf : α ((f.1 : R[X]).derivative) = c := by
    have h := congrArg E hk
    simpa only [E,x,kerCotangentToTensor_toCotangent,LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,
      polynomialEquiv_D,derivative_X,TensorProduct.AlgebraTensorModule.rid_tmul,
      Algebra.smul_def,map_one,mul_one,one_mul] using h
  refine ⟨α q,?_⟩
  rw [hq,derivative_mul,map_add,map_mul,map_mul,hp,zero_mul,add_zero] at hf
  exact hf

/-- Specialization along the actual section uses that same integral
multiple. The output is not an assumed annihilator/divisibility datum. -/
theorem specialized_derivative_dvd {O : Type*} [CommRing O]
    (β : B →+* O) (α : R[X] →ₐ[R] B) (surj : Function.Surjective α)
    (p : R[X]) (hp : α p = 0) (kernel : ∀ q : R[X], α q = 0 → p ∣ q)
    (M : ℕ) (kill : M • D R B (α X) = 0) :
    ∃ w : O, β (α p.derivative) * w = (M:O) := by
  have h : (M:B) • D R B (α X) = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul B] using kill
  obtain ⟨b,hb⟩ := derivative_dvd_of_kills_dx α surj p hp kernel (M:B) h
  exact ⟨β b, by simpa only [map_mul,map_natCast] using congrArg β hb⟩
end Monogenic

section IntegralTransport
variable {R T B : Type*} [CommRing R] [CommRing T] [CommRing B]
variable [Algebra R T] [Algebra R B]

/-- A true integral closed branch of the total M-torsion algebra inherits
its differential annihilator. A generic identification or mere relative
finite flatness does not give the surjectivity premise. -/
theorem kills_of_integral_quotient [Algebra T B] [IsScalarTower R T B]
    (surj : Function.Surjective (algebraMap T B))
    (M : ℕ) (kill : ∀ ω : KaehlerDifferential R T, M • ω = 0) :
    ∀ ω : KaehlerDifferential R B, M • ω = 0 := by
  intro ω
  obtain ⟨η,rfl⟩ := map_surjective_of_surjective R R T B surj ω
  rw [← map_nsmul,kill,map_zero]

/-- Descend that differential annihilator through an actual faithfully
flat formally étale sign torsor. This is a check on the integral map,
not an identification of invariant algebras solely on points. -/
theorem kills_of_etale_cover [Algebra B T] [IsScalarTower R B T]
    [Algebra.FormallyEtale B T] [Module.FaithfullyFlat B T]
    (M : ℕ) (kill : ∀ ω : KaehlerDifferential R T, M • ω = 0) :
    ∀ ω : KaehlerDifferential R B, M • ω = 0 := by
  intro ω
  apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff B (KaehlerDifferential R B) (A:=T) (M • ω)).mp
  let f : KaehlerDifferential R B →ₗ[B] T ⊗[B] KaehlerDifferential R B :=
    TensorProduct.mk B T (KaehlerDifferential R B) 1
  change f (M • ω) = 0
  apply (tensorKaehlerEquivOfFormallyEtale R B T).injective
  rw [map_zero,map_nsmul,map_nsmul,kill]

end IntegralTransport
end SelectedMonogenicCotangentDivisibility318

#print axioms SelectedMonogenicCotangentDivisibility318.derivative_dvd_of_kills_dx
#print axioms SelectedMonogenicCotangentDivisibility318.specialized_derivative_dvd
#print axioms SelectedMonogenicCotangentDivisibility318.kills_of_integral_quotient
#print axioms SelectedMonogenicCotangentDivisibility318.kills_of_etale_cover
