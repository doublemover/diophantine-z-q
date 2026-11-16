module
public import FourRootOrder318
public import KummerTensorField318
public section
noncomputable section
namespace DistinctContactGenericField318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 900000
variable {F : Type*} [Field F] [CharZero F] (a d : Fin 4 → F)
@[expose] def coefficient (i : Fin 4) : F[X] := C (d i) * (X-C (a i))
@[expose] def parameter (i : Fin 4) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (coefficient a d i)
abbrev Source := FourRootOrder318.Order (coefficient a d)

theorem product_nonsquare (ha : Function.Injective a) (hd : ∀ i, d i ≠ 0)
    (s : Finset (Fin 4)) (hs : s.Nonempty) :
    ¬IsSquare (∏ i ∈ s, parameter a d i) := by
  have hp : (∏ i ∈ s, parameter a d i) = algebraMap F[X] (RatFunc F)
      (C (∏ i ∈ s, d i) * ∏ i ∈ s, (X-C (a i))) := by
    simp only [parameter, coefficient, ←map_prod, Finset.prod_mul_distrib]
  rw [hp]
  exact LinearContactSquareclass318.twisted_product_nonsquare a ha s hs _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))

theorem independent (ha : Function.Injective a) (hd : ∀ i, d i ≠ 0) :
    QuadraticTower318.Independent (parameter a d) :=
  SourceKummerField318.independent_of_products _ (product_nonsquare a d ha hd)

/-- The entire sixteen-dimensional tensor presentation is a field after the
actual rational-function base change. No generic component is selected. -/
theorem generic_field (ha : Function.Injective a) (hd : ∀ i, d i ≠ 0) :
    IsField (KummerTensorField318.Raw (parameter a d)) := by
  letI : Fact (QuadraticTower318.Independent (parameter a d)) := ⟨independent a d ha hd⟩
  exact KummerTensorField318.actual_field _

@[expose] def genericFiber : RatFunc F ⊗[F[X]] Source a d ≃ₐ[RatFunc F]
    KummerTensorField318.Raw (parameter a d) := FourRootOrder318.baseChange _ _
@[expose] def embedding : Source a d →+* KummerTensorField318.Raw (parameter a d) :=
  (genericFiber a d).toRingHom.comp
    (Algebra.TensorProduct.includeRight : Source a d →ₐ[F[X]]
      RatFunc F ⊗[F[X]] Source a d).toRingHom

theorem embedding_injective : Function.Injective (embedding a d) := by
  letI : Module.Free F[X] (Source a d) := (FourRootOrder318.finite_free _).2
  exact (genericFiber a d).injective.comp
    (Algebra.TensorProduct.includeRight_injective (R := F[X]) (A := RatFunc F)
      (B := Source a d) (IsFractionRing.injective F[X] (RatFunc F)))

theorem source_domain (ha : Function.Injective a) (hd : ∀ i, d i ≠ 0) :
    IsDomain (Source a d) := by
  letI : Field (KummerTensorField318.Raw (parameter a d)) :=
    (generic_field a d ha hd).toField
  exact Function.Injective.isDomain (embedding a d) (embedding_injective a d)
end DistinctContactGenericField318
