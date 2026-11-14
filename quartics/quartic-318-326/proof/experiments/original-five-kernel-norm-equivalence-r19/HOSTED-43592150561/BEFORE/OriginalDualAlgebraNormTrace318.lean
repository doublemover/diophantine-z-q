module
public import OriginalRightTensorNormTrace318
public section
noncomputable section
namespace OriginalDualAlgebraNormTrace318
open scoped TensorProduct
open TrivSqZeroExt
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
/-- The actual dual coefficient map already used to identify the original
fiber-product ring, not the augmentation that kills epsilon. -/
@[expose] def actualAlgebra : Algebra (DualNumber R) (DualNumber S) :=
  (DualNumberScalarExtension318.baseMap R S).toRingHom.toAlgebra
attribute [local instance] actualAlgebra
/-- Upgrade the SAME original tensor/dual equivalence, fixing every element
of the actual dual base ring by its original right projection. -/
@[expose] def equivalence : (S ⊗[R] DualNumber R) ≃ₐ[DualNumber R] DualNumber S where
  __ := (DualNumberScalarExtension318.equivalence R S).toRingEquiv
  commutes' d := DualNumberScalarExtension318.forward_right R S d
lemma infinitesimal_eq (x : S) :
    InfinitesimalUnitCocycle318.infinitesimal (DualNumber.eps : DualNumber S)
      DualNumber.eps_mul_eps (algebraMap S (DualNumber S) x) = SquareZeroUnit318.unit S x := by
  apply Units.ext
  change 1 + DualNumber.eps * algebraMap S (DualNumber S) x = 1 + inr x
  rw [TrivSqZeroExt.algebraMap_eq_inl]
  congr 1
  rw [mul_comm, TrivSqZeroExt.inl_mul_eq_smul, DualNumber.inr_eq_smul_eps]
variable [Module.Free R S] [Module.Finite R S]
/-- The genuine finite-free module structure is transported from the original
finite-free scalar extension through the same two original algebra maps. -/
lemma finite_free : Module.Free (DualNumber R) (DualNumber S) ∧
    Module.Finite (DualNumber R) (DualNumber S) := by
  let e := (OriginalRightTensorNormTrace318.commute R S (DualNumber R)).trans (equivalence R S)
  exact ⟨Module.Free.of_equiv e.toLinearEquiv, Module.Finite.equiv e.toLinearEquiv⟩
lemma norm_inl (x : S) : Algebra.norm (DualNumber R) (inl x : DualNumber S) =
    inl (Algebra.norm R x) := by
  have hx : equivalence R S (x ⊗ₜ[R] 1) = (inl x : DualNumber S) :=
    DualNumberScalarExtension318.equivalence_left R S x
  rw [← hx, Algebra.norm_eq_of_algEquiv (equivalence R S) (x ⊗ₜ[R] 1),
    OriginalRightTensorNormTrace318.norm_coefficient,
    TrivSqZeroExt.algebraMap_eq_inl]
/-- The determinant norm of the ORIGINAL dual base-change algebra sends the
OLD actual1+epsilon unit to the OLD actual1+epsilon unit of the ORIGINAL trace.
No integrality or reducedness of the test ring is required. -/
lemma norm_unit (x : S) :
    Units.map (Algebra.norm (DualNumber R)) (SquareZeroUnit318.unit S x) =
      SquareZeroUnit318.unit R (Algebra.trace R S x) := by
  let z : (S ⊗[R] DualNumber R)ˣ := InfinitesimalUnitCocycle318.infinitesimal
    (algebraMap (DualNumber R) (S ⊗[R] DualNumber R) DualNumber.eps)
    (by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]) (x ⊗ₜ[R] 1)
  have hz : equivalence R S z.val = (SquareZeroUnit318.unit S x).val := by
    change DualNumberScalarExtension318.equivalence R S
      (1 + (1 ⊗ₜ[R] DualNumber.eps) * (x ⊗ₜ[R] 1)) = _
    rw [map_add, map_one, map_mul, DualNumberScalarExtension318.equivalence_epsilon,
      DualNumberScalarExtension318.equivalence_left]
    exact congrArg Units.val (infinitesimal_eq S x)
  have hn := congrArg Units.val
    (OriginalRightTensorNormTrace318.norm_infinitesimal R S (DualNumber R)
      DualNumber.eps DualNumber.eps_mul_eps x)
  apply Units.ext
  change Algebra.norm (DualNumber R) (SquareZeroUnit318.unit S x).val = _
  rw [← hz, Algebra.norm_eq_of_algEquiv (equivalence R S) z.val]
  exact hn.trans (congrArg Units.val (infinitesimal_eq R (Algebra.trace R S x)))
end OriginalDualAlgebraNormTrace318
