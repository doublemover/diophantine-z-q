module
public import OriginalAffineFrameSum318
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace OriginalAffineParameterSquare318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R A B S : CommRingCat.{u}) [Algebra R A] [Algebra R S] (f : A ⟶ B)
local instance : Algebra R B := (f.hom.comp (algebraMap R A)).toAlgebra

@[expose] def coefficientMap : A →ₐ[R] B where
  __ := f.hom
  commutes' r := rfl
@[expose] def source : CommRingCat.{u} := CommRingCat.of (S ⊗[R] A)
@[expose] def target : CommRingCat.{u} := CommRingCat.of (S ⊗[R] B)
@[expose] def sourceMap : A ⟶ source R A S :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R:=R) (A:=S) (B:=A)).toRingHom
@[expose] def targetMap : B ⟶ target R A B S f :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R:=R) (A:=S) (B:=B)).toRingHom
@[expose] def chartMap : source R A S ⟶ target R A B S f :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R S) (coefficientMap R A B f)).toRingHom

lemma square : Spec.map (chartMap R A B S f) ≫ Spec.map (sourceMap R A S) =
    Spec.map (targetMap R A B S f) ≫ Spec.map f := by
  rw [← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change Algebra.TensorProduct.map (AlgHom.id R S) (coefficientMap R A B f)
    ((1:S) ⊗ₜ[R] a) = (1:S) ⊗ₜ[R] f.hom a
  rw [Algebra.TensorProduct.map_tmul,AlgHom.id_apply]
  rfl

lemma source_coefficient (s : S) : chartMap R A B S f (s ⊗ₜ[R] (1:A))=s ⊗ₜ[R] (1:B) := by
  change Algebra.TensorProduct.map (AlgHom.id R S) (coefficientMap R A B f)
    (s ⊗ₜ[R] (1:A))=_
  rw [Algebra.TensorProduct.map_tmul,AlgHom.id_apply,map_one]

variable (L : Line (Spec A)) (N : Line (Spec B))
  (e : (Scheme.Modules.pullback (Spec.map f)).obj L.object ≅ N.object)
  (v : OriginalLineAffineModel318.sections B N ≃ₗ[B] B)

/-- The whole actual affine square under coefficient parameter extension,
with the literal original line/frame and both tensor factors retained. -/
abbrev coordinate := OriginalAffineFrameSum318.coordinate A B (source R A S) (target R A B S f)
  f (sourceMap R A S) (chartMap R A B S f) (targetMap R A B S f) (square R A B S f) L N e v

lemma coefficient_formula {ι : Type*} [Fintype ι] (a : ι → S)
    (m : ι → OriginalLineAffineModel318.sections A L) :
    coordinate R A B S f L N e v
      (∑ j, (a j ⊗ₜ[R] (1:A)) • OriginalAffineLinePathSections318.restriction
        (sourceMap R A S) L
        (OriginalAffineFrameSquare318.sourceLine A (source R A S) (sourceMap R A S) L)
        (Iso.refl _) (m j)) =
      ∑ j, a j ⊗ₜ[R] v (OriginalAffineLinePathSections318.restriction f L N e (m j)) := by
  rw [OriginalAffineFrameSum318.sum_formula]
  apply Finset.sum_congr rfl
  intro j hj
  rw [source_coefficient]
  change (a j ⊗ₜ[R] (1:B)) * ((1:S) ⊗ₜ[R] _)=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
end OriginalAffineParameterSquare318
