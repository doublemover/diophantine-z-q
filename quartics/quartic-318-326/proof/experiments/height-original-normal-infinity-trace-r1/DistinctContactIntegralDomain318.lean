module
public import DistinctContactGenericField318
public import Mathlib.Algebra.Polynomial.AlgebraMap
public section
noncomputable section
namespace DistinctContactIntegralDomain318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 900000
variable (R F : Type*) [CommRing R] [Field F] [CharZero F] [Algebra R F]
variable (a d : Fin 4 → R)
@[expose] def coefficient (i : Fin 4) : R[X] := C (d i) * (X-C (a i))
abbrev Source := FourRootOrder318.Order (coefficient R a d)
@[expose] def polynomialMap : R[X] →+* F[X] := Polynomial.mapRingHom (algebraMap R F)
local instance polynomialAlgebra : Algebra R[X] F[X] := (polynomialMap R F).toAlgebra
@[expose] def mappedContacts : Fin 4 → F := fun i => algebraMap R F (a i)
@[expose] def mappedTwists : Fin 4 → F := fun i => algebraMap R F (d i)

theorem coefficient_map (i : Fin 4) :
    algebraMap R[X] F[X] (coefficient R a d i) =
      DistinctContactGenericField318.coefficient (mappedContacts R F a) (mappedTwists R F d) i := by
  change Polynomial.map (algebraMap R F) (C (d i)*(X-C (a i))) = _
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X]
  rfl
@[expose] def presentationEquiv {b c : Fin 4 → F[X]} (h : b=c) :
    FourRootOrder318.Order b ≃ₐ[F[X]] FourRootOrder318.Order c := by
  subst c
  exact AlgEquiv.refl
@[expose] def baseChange : F[X] ⊗[R[X]] Source R a d ≃ₐ[F[X]]
    DistinctContactGenericField318.Source (mappedContacts R F a) (mappedTwists R F d) :=
  (FourRootOrder318.baseChange (coefficient R a d) F[X]).trans
    (presentationEquiv F (funext (coefficient_map R F a d)))
@[expose] def embedding : Source R a d →+*
    DistinctContactGenericField318.Source (mappedContacts R F a) (mappedTwists R F d) :=
  (baseChange R F a d).toRingHom.comp
    (Algebra.TensorProduct.includeRight : Source R a d →ₐ[R[X]]
      F[X] ⊗[R[X]] Source R a d).toRingHom

theorem embedding_injective (hR : Function.Injective (algebraMap R F)) :
    Function.Injective (embedding R F a d) := by
  letI : Module.Free R[X] (Source R a d) := (FourRootOrder318.finite_free _).2
  exact (baseChange R F a d).injective.comp
    (Algebra.TensorProduct.includeRight_injective (R := R[X]) (A := F[X])
      (B := Source R a d) (Polynomial.map_injective (algebraMap R F) hR))

/-- Arbitrary nonzero integral twists are allowed, including uniformizer
powers. The injection into the actual coefficient field is retained. -/
theorem source_domain (hR : Function.Injective (algebraMap R F))
    (ha : Function.Injective a) (hd : ∀ i, d i ≠ 0) : IsDomain (Source R a d) := by
  have haF : Function.Injective (mappedContacts R F a) := hR.comp ha
  have hdF : ∀ i, mappedTwists R F d i ≠ 0 := fun i => by
    simpa only [mappedTwists, map_zero] using hR.ne (hd i)
  letI := DistinctContactGenericField318.source_domain
    (mappedContacts R F a) (mappedTwists R F d) haF hdF
  exact Function.Injective.isDomain (embedding R F a d) (embedding_injective R F a d hR)
end DistinctContactIntegralDomain318
