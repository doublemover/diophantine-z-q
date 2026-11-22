module
public import SelectedPrimitivePowerBasis318
public import SelectedMonicReducedFiber318
public section
noncomputable section
open Polynomial
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318
open SelectedPrimitiveXCharacteristic318 SelectedPrimitivePowerBasis318

namespace SelectedPrimitiveSimpleChart318

private theorem derivative_unit_subalgebra {A B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (S₀ : Subalgebra A B)
    (hret : ∃ L : B →ₗ[A] S₀, L.comp S₀.val.toLinearMap = LinearMap.id)
    (p : A[X]) (hp : p.Monic) (e : AdjoinRoot p ≃ₐ[A] S₀) :
    IsUnit (aeval (e (AdjoinRoot.root p)) p.derivative) := by
  obtain ⟨L,hL⟩ := hret
  exact SelectedMonicReducedFiber318.derivative_unit
    (R := A) (B := B) (C := ↥S₀) S₀.val L hL p hp e

variable (M : ℕ) (I : Ideal (D M))
variable (τ : (D M ⧸ I) →ₐ[R M] (D M ⧸ I))
variable (hτ : τ.comp (q M I) = (q M I).comp (sign M))
variable (hinv : τ.comp τ = AlgHom.id (R M) (D M ⧸ I))
variable [Module.Finite (R M) (D M ⧸ I)] [Algebra.Etale (R M) (D M ⧸ I)]

private theorem derivative_unit_fixed (hInv : τ.comp τ = AlgHom.id (R M) (D M ⧸ I))
    (p : (R M)[X]) (hp : p.Monic) (e : AdjoinRoot p ≃ₐ[R M] S M I τ) :
    IsUnit (aeval (e (AdjoinRoot.root p)) p.derivative) :=
  @derivative_unit_subalgebra (R M) (D M ⧸ I)
    (inferInstance : CommRing (R M)) (inferInstance : CommRing (D M ⧸ I))
    (inferInstance : Algebra (R M) (D M ⧸ I))
    (inferInstance : Algebra.Etale (R M) (D M ⧸ I))
    (SelectedPrimitiveXCharacteristic318.S M I τ) (reynolds M I τ hInv) p hp e

include hinv in
/-- The actual fixed quotient has a powers basis on the same x and the
actual characteristic polynomial is monic with a unit derivative there.
Only the finite étale condition of its original unsigned coordinate ring
is used, not finite étaleness of this fixed quotient. -/
theorem characteristic_simple (hM : M ≠ 0) :
    ∃ pb : PowerBasis (R M) (fixed M I τ), pb.gen = coordinate M I τ hτ ∧
      (letI : Module.Free (R M) (fixed M I τ) := Module.Free.of_basis pb.basis
       letI : Module.Finite (R M) (fixed M I τ) := pb.finite
       (charPolynomial M I τ hτ).Monic ∧
       ∃ e : AdjoinRoot (charPolynomial M I τ hτ) ≃ₐ[R M] fixed M I τ,
         e (AdjoinRoot.root (charPolynomial M I τ hτ)) = coordinate M I τ hτ ∧
         IsUnit (aeval (coordinate M I τ hτ) (charPolynomial M I τ hτ).derivative)) := by
  letI : IsDomain (R M) := base_domain M hM
  obtain ⟨pb,hpb⟩ := powers M I τ hτ hinv hM
  refine ⟨pb,hpb,?_⟩
  letI : Module.Free (R M) (fixed M I τ) := Module.Free.of_basis pb.basis
  letI : Module.Finite (R M) (fixed M I τ) := pb.finite
  let p := charPolynomial M I τ hτ
  let e := characteristicEquiv M I τ hτ
  have hp : p.Monic := monic_charPolynomial M I τ hτ
  have hx : e (AdjoinRoot.root p) = coordinate M I τ hτ := characteristicEquiv_root M I τ hτ
  change p.Monic ∧ ∃ i : AdjoinRoot p ≃ₐ[R M] fixed M I τ,
    i (AdjoinRoot.root p) = coordinate M I τ hτ ∧
    IsUnit (aeval (coordinate M I τ hτ) p.derivative)
  refine ⟨hp,e,hx,?_⟩
  rw [← hx]
  exact derivative_unit_fixed M I τ hinv p hp e

end SelectedPrimitiveSimpleChart318

#print axioms SelectedPrimitiveSimpleChart318.characteristic_simple
