module
public import SourceKummerField318
public import ContactGenericFiber318
public section
noncomputable section
namespace KummerTensorField318
set_option maxHeartbeats 900000
open scoped TensorProduct
open QuadraticPresentation318 QuadraticTower318
variable {F:Type*} [Field F] [CharZero F] (a:Fin 4→F)
abbrev Raw:=(RootRing (a 0)⊗[F]RootRing (a 1))⊗[F](RootRing (a 2)⊗[F]RootRing (a 3))

/-- The actual tensor base change of a polynomial quotient is identified with
the explicit quadratic algebra over the new base. -/
@[expose] def baseQuadratic (A:Type*) [CommRing A] [Algebra F A] (b:F) :
    A⊗[F]RootRing b ≃ₐ[F] QuadraticAlgebra A (algebraMap F A b) 0 :=
  ((ContactGenericFiber318.rootBaseChange (S:=A) b).trans
    (presentationEquiv (algebraMap F A b)).symm).restrictScalars F

@[expose] def pairEquiv : RootRing (a 0)⊗[F]RootRing (a 1) ≃ₐ[F] L2 a :=
  (Algebra.TensorProduct.congr (presentationEquiv (a 0)).symm
    (AlgEquiv.refl : RootRing (a 1)≃ₐ[F]RootRing (a 1))).trans
      (baseQuadratic (L1 a) (a 1))

@[expose] def tripleEquiv : (RootRing (a 0)⊗[F]RootRing (a 1))⊗[F]RootRing (a 2) ≃ₐ[F] L3 a :=
  (Algebra.TensorProduct.congr (pairEquiv a)
    (AlgEquiv.refl : RootRing (a 2)≃ₐ[F]RootRing (a 2))).trans
      (baseQuadratic (L2 a) (a 2))

/-- The real four-polynomial tensor algebra, not an abstract field with the
same dimension, is identified with the constructed iterated quadratic field. -/
@[expose] def rawEquiv : Raw a≃ₐ[F]L4 a :=
  (Algebra.TensorProduct.assoc F F F (RootRing (a 0)⊗[F]RootRing (a 1))
    (RootRing (a 2)) (RootRing (a 3))).symm.trans
      ((Algebra.TensorProduct.congr (tripleEquiv a)
        (AlgEquiv.refl : RootRing (a 3)≃ₐ[F]RootRing (a 3))).trans
          (baseQuadratic (L3 a) (a 3)))

theorem actual_field [Fact (Independent a)] : IsField (Raw a) := by
  exact (rawEquiv a).toRingEquiv.isField (Field.toIsField _)

theorem actual_degree [Fact (Independent a)] : Module.finrank F (Raw a)=16 := by
  rw [(rawEquiv a).toLinearEquiv.finrank_eq]
  exact degree_sixteen a

theorem source_raw_field (c:Fin 4→ℚˣ) : IsField (Raw (SourceKummerField318.parameter c)) :=
  actual_field _
theorem source_raw_degree (c:Fin 4→ℚˣ) :
    Module.finrank (RatFunc ℚ) (Raw (SourceKummerField318.parameter c))=16 := actual_degree _
end KummerTensorField318
