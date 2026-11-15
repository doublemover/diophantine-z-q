module
public import OriginalAffineComposedSection318
public import OriginalCoefficientTensor318
public section
noncomputable section
namespace OriginalCoefficientTensorSection318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped BigOperators TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (K R S B : CommRingCat.{u}) [Algebra K R] [Algebra K S] [Algebra K B]
  (q : R →ₐ[K] S)
local instance : Algebra R S := q.toAlgebra
local instance : IsScalarTower K R S := IsScalarTower.of_algebraMap_eq' (by ext a; exact (q.commutes a).symm)
local notation "A" => OriginalCoefficientTensor318.oldRing K R B
local notation "AS" => OriginalCoefficientTensor318.pushout K R S B q
local notation "C" => OriginalCoefficientTensor318.newRing K S B

@[expose] def inclusion : A ⟶ AS :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R:=R) (A:=S) (B:=A)).toRingHom
@[expose] def relabel : AS ⟶ C := CommRingCat.ofHom
  (OriginalCoefficientTensor318.ringEquivalence K R S B q).toRingHom
@[expose] def original : A ⟶ C := RelativeCoefficientChange318.ringMap K R S B q

lemma path : Spec.map (relabel K R S B q) ≫ Spec.map (inclusion K R S B q) =
    Spec.map (original K R S B q) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact OriginalCoefficientTensor318.ringEquivalence_right K R S B q a

variable (L : Line (Spec A)) (N : Line (Spec C))
  (e : (Scheme.Modules.pullback (Spec.map (original K R S B q))).obj L.object ≅ N.object)

/-- Comparison from literal coefficient-only tensor chart to the ACTUAL
original chart algebra, including its true geometric line pullback path. -/
abbrev comparison := OriginalAffineComposedSection318.comparison A AS C
  (inclusion K R S B q) (relabel K R S B q) (original K R S B q) (path K R S B q) L N e
abbrev restriction := OriginalAffineComposedSection318.restriction A AS C
  (inclusion K R S B q) (relabel K R S B q) (original K R S B q) (path K R S B q) L N e

lemma expansion {ι : Type*} [Fintype ι] (a : ι → S)
    (m : ι → OriginalLineAffineModel318.sections A L) :
    restriction K R S B q L N e
      (∑ j, (a j ⊗ₜ[R] (1:A)) • OriginalAffineLinePathSections318.restriction
        (inclusion K R S B q) L
        (OriginalAffineComposedSection318.intermediate A AS (inclusion K R S B q) L)
        (Iso.refl _) (m j)) =
    ∑ j, (a j ⊗ₜ[K] (1:B)) • OriginalAffineLinePathSections318.restriction
      (original K R S B q) L N e (m j) := by
  rw [OriginalAffineComposedSection318.finite_sum]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact (OriginalCoefficientTensor318.ringEquivalence K R S B q).commutes (a j)
end OriginalCoefficientTensorSection318
