module
public import SelectedPrimitiveFixedX318
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.FiniteType
public section
noncomputable section
open Polynomial
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318

namespace SelectedPrimitiveXCharacteristic318

variable (n : ℕ) (I : Ideal (D n))
variable (τ : (D n ⧸ I) →ₐ[R n] (D n ⧸ I))
variable (hτ : τ.comp (q n I) = (q n I).comp (sign n))

abbrev S := fixed n I τ

/-- Literal x in the actual fixed coordinate algebra, with a proof that the
genuine involution fixes it. -/
@[expose] def coordinate : S n I τ :=
  ⟨xbar n I, (fixed_iff_polynomial n I τ hτ _).mpr ⟨Polynomial.X,aeval_X _⟩⟩

variable [Module.Free (R n) (S n I τ)] [Module.Finite (R n) (S n I τ)]

/-- This is the characteristic polynomial of multiplication by the literal
coordinate on the fixed algebra. Freeness is a separate native producer;
the definition does not stipulate a polynomial with desired properties. -/
@[expose] def charPolynomial : (R n)[X] :=
  (Algebra.lmul (R n) (S n I τ) (coordinate n I τ hτ)).charpoly

theorem monic_charPolynomial : (charPolynomial n I τ hτ).Monic :=
  LinearMap.charpoly_monic _

theorem coordinate_root :
    aeval (coordinate n I τ hτ) (charPolynomial n I τ hτ) = 0 :=
  Algebra.aeval_self_charpoly_lmul _

/-- All genuine sign-quotient points satisfy the same specialized
characteristic polynomial; this is natural in the test algebra. -/
theorem evaluated_coordinate_root {T : Type} [CommRing T] [Algebra (R n) T]
    (f : S n I τ →ₐ[R n] T) :
    aeval (f (coordinate n I τ hτ)) (charPolynomial n I τ hτ) = 0 := by
  rw [Polynomial.aeval_algHom_apply,coordinate_root,map_zero]

/-- Coefficient specialization agrees with the actual base-changed
multiplication operator, before any choice of splitting or root labels. -/
theorem charPolynomial_baseChange (T : Type) [CommRing T] [Algebra (R n) T] :
    ((Algebra.lmul (R n) (S n I τ) (coordinate n I τ hτ)).baseChange T).charpoly =
      (charPolynomial n I τ hτ).map (algebraMap (R n) T) :=
  LinearMap.charpoly_baseChange _ _

private theorem characteristic_eval_span_zero (p : (R n)[X])
    (hp : p ∈ Ideal.span {charPolynomial n I τ hτ}) :
    aeval (coordinate n I τ hτ) p = 0 := by
  let ev : (R n)[X] →ₐ[R n] S n I τ := aeval (coordinate n I τ hτ)
  let K : Ideal (R n)[X] := RingHom.ker ev.toRingHom
  have hk : Ideal.span {charPolynomial n I τ hτ} ≤ K :=
    (Ideal.span_singleton_le_iff_mem K).2 (RingHom.mem_ker.2 (coordinate_root n I τ hτ))
  exact RingHom.mem_ker.mp (hk hp)

/-- The actual fixed algebra is a quotient of the characteristic-polynomial
root algebra. Injectivity is deliberately not asserted from only roothood. -/
@[expose] def fromAdjoinRoot :
    AdjoinRoot (charPolynomial n I τ hτ) →ₐ[R n] S n I τ :=
  Ideal.Quotient.liftₐ (Ideal.span {charPolynomial n I τ hτ})
    (aeval (coordinate n I τ hτ)) (by exact characteristic_eval_span_zero n I τ hτ)

private theorem fromAdjoinRoot_mk (p : (R n)[X]) :
    fromAdjoinRoot n I τ hτ (AdjoinRoot.mk (charPolynomial n I τ hτ) p) =
      aeval (coordinate n I τ hτ) p := by
  have he := Ideal.Quotient.liftₐ_comp (Ideal.span {charPolynomial n I τ hτ})
    (aeval (coordinate n I τ hτ)) (characteristic_eval_span_zero n I τ hτ)
  have hx := DFunLike.congr_fun he p
  change fromAdjoinRoot n I τ hτ (AdjoinRoot.mk (charPolynomial n I τ hτ) p) =
    aeval (coordinate n I τ hτ) p at hx
  exact hx

theorem fromAdjoinRoot_root :
    fromAdjoinRoot n I τ hτ (AdjoinRoot.root (charPolynomial n I τ hτ)) =
      coordinate n I τ hτ := by
  rw [← AdjoinRoot.mk_X,fromAdjoinRoot_mk,Polynomial.aeval_X]

theorem fromAdjoinRoot_surjective : Function.Surjective (fromAdjoinRoot n I τ hτ) := by
  intro b
  obtain ⟨p,hp⟩ := (fixed_iff_polynomial n I τ hτ b.val).mp b.property
  refine ⟨AdjoinRoot.mk (charPolynomial n I τ hτ) p,?_⟩
  apply Subtype.ext
  change (fixed n I τ).val
    (fromAdjoinRoot n I τ hτ (AdjoinRoot.mk (charPolynomial n I τ hτ) p)) = b.val
  rw [fromAdjoinRoot_mk]
  exact (Polynomial.aeval_algHom_apply (fixed n I τ).val (coordinate n I τ hτ) p).symm.trans hp

/-- Once the actual coordinate algebra is known to be free, the quotient
is exactly the characteristic-polynomial root algebra, not just an image.
Cayley–Hamilton and the two equal finite ranks supply injectivity. -/
theorem fromAdjoinRoot_bijective [Nontrivial (R n)] :
    Function.Bijective (fromAdjoinRoot n I τ hτ) := by
  let p := charPolynomial n I τ hτ
  have hp : p.Monic := monic_charPolynomial n I τ hτ
  letI : Module.Free (R n) (AdjoinRoot p) := hp.free_adjoinRoot
  letI : Module.Finite (R n) (AdjoinRoot p) := hp.finite_adjoinRoot
  apply OrzechProperty.bijective_of_surjective_of_finrank_le (fromAdjoinRoot n I τ hτ).toLinearMap
    (fromAdjoinRoot_surjective n I τ hτ)
  have hd : p.natDegree = Module.finrank (R n) (S n I τ) := LinearMap.charpoly_natDegree _
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' hp).basis,Fintype.card_fin]
  change p.natDegree ≤ Module.finrank (R n) (S n I τ)
  exact hd.le

@[expose] def characteristicEquiv [Nontrivial (R n)] :
    AdjoinRoot (charPolynomial n I τ hτ) ≃ₐ[R n] S n I τ :=
  AlgEquiv.ofBijective (fromAdjoinRoot n I τ hτ) (fromAdjoinRoot_bijective n I τ hτ)

theorem characteristicEquiv_root [Nontrivial (R n)] :
    characteristicEquiv n I τ hτ (AdjoinRoot.root (charPolynomial n I τ hτ)) =
      coordinate n I τ hτ := fromAdjoinRoot_root n I τ hτ

end SelectedPrimitiveXCharacteristic318

#print axioms SelectedPrimitiveXCharacteristic318.coordinate_root
#print axioms SelectedPrimitiveXCharacteristic318.charPolynomial_baseChange
#print axioms SelectedPrimitiveXCharacteristic318.characteristicEquiv_root
