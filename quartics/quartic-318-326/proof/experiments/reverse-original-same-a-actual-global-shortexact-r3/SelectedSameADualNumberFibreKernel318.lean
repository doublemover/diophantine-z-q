module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The fibre reduction presented by the actual affine pullback

The structural map kills precisely the image of the same dual-number
parameter, without assuming flatness. The tensor projection is tracked
through the quotient equivalence, so an abstract ring isomorphism
alone cannot masquerade as the established fibre reduction.
-/

public section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace SelectedSameADualNumberFibreKernel318

variable (k C : Type*) [CommRing k] [CommRing C]

abbrev D := TrivSqZeroExt k k
abbrev ε : D k := TrivSqZeroExt.inr 1
abbrev projection : D k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

def baseAlgebra : Algebra (D k) k := TrivSqZeroExt.algebraBase k k
attribute [local instance] baseAlgebra

/-- The exact structural reduction of the base has kernel (epsilon). -/
theorem projection_ker :
    RingHom.ker (projection k) = Ideal.span ({ε k} : Set (D k)) := by
  ext x
  constructor
  · intro hx
    have h : x.fst = 0 := RingHom.mem_ker.mp hx
    refine Ideal.mem_span_singleton.mpr ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    rw [TrivSqZeroExt.inr_mul_inl, op_smul_eq_smul, smul_eq_mul, mul_one]
    exact TrivSqZeroExt.ext (by rw [TrivSqZeroExt.fst_inr, h]) (TrivSqZeroExt.snd_inr _).symm
  · intro hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
    apply RingHom.mem_ker.mpr
    change (ε k * b).fst = 0
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inr, zero_mul]

private abbrev I : Ideal (D k) := RingHom.ker (projection k)

private theorem projection_rightInverse :
    Function.RightInverse (fun a : k => (TrivSqZeroExt.inl a : D k)) (projection k) := by
  intro a
  exact TrivSqZeroExt.fst_inl _ _

private noncomputable def baseEquiv : ((D k) ⧸ I k) ≃ₐ[D k] k where
  __ := RingHom.quotientKerEquivOfRightInverse (projection_rightInverse k)
  commutes' a := by
    change RingHom.quotientKerEquivOfRightInverse (projection_rightInverse k)
      (Ideal.Quotient.mk (I k) a) = projection k a
    rw [RingHom.quotientKerEquivOfRightInverse.apply, RingHom.kerLift_mk]

variable [Algebra (D k) C]

private abbrev J : Ideal C := Ideal.map (algebraMap (D k) C) (I k)

/-- The genuine affine pullback tensor ring is the quotient by the
extension of the original base kernel. -/
private noncomputable def quotientTensor :
    (C ⧸ J k C) ≃+* (C ⊗[D k] k) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (I k)).toRingEquiv.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl (D k) C) (baseEquiv k)).toRingEquiv

private theorem quotientTensor_mk (c : C) :
    quotientTensor k C (Ideal.Quotient.mk (J k C) c) = c ⊗ₜ[D k] (1 : k) := by
  unfold quotientTensor
  change (Algebra.TensorProduct.congr (AlgEquiv.refl (D k) C) (baseEquiv k))
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (I k)
      (Ideal.Quotient.mk (J k C) c)) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  simp

private theorem J_eq : J k C = Ideal.span ({algebraMap (D k) C (ε k)} : Set C) := by
  unfold J I
  rw [projection_ker, Ideal.map_span, Set.image_singleton]

/-- This conclusion is tied to the specific first tensor leg. When f is the
actual coordinate map of the affine fibre, the compatibility is obtained
from the first projection of the scheme pullback. -/
theorem actualReduction_surjective_ker {B : Type*} [CommRing B]
    (f : C →+* B) (e : (C ⊗[D k] k) ≃+* B)
    (hf : ∀ c, f c = e (c ⊗ₜ[D k] (1 : k))) :
    Function.Surjective f ∧
      RingHom.ker f = Ideal.span ({algebraMap (D k) C (ε k)} : Set C) := by
  let v := (quotientTensor k C).trans e
  have he (c : C) : f c = v (Ideal.Quotient.mk (J k C) c) := by
    change f c = e (quotientTensor k C (Ideal.Quotient.mk (J k C) c))
    rw [quotientTensor_mk]
    exact hf c
  constructor
  · intro b
    obtain ⟨z, hz⟩ := v.surjective b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨c, (he c).trans hz⟩
  · rw [← J_eq k C]
    ext c
    rw [RingHom.mem_ker, he]
    constructor
    · intro h
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply v.injective
      rw [h, map_zero]
    · intro h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

section GeometricFibre

universe u
variable (K A B : Type u) [CommRing K] [CommRing A] [CommRing B]
  [Algebra (D K) A]

abbrev S (T : Type u) [CommRing T] : Scheme.{u} := Spec (CommRingCat.of T)

abbrev sp {T V : Type u} [CommRing T] [CommRing V] (f : T →+* V) : S V ⟶ S T :=
  Spec.map (CommRingCat.ofHom f)

/-- The actual affine scheme pullback supplies the marked tensor isomorphism
and its first-projection beta. No ring isomorphism is assumed in this endpoint. -/
theorem actualAffineFibre_ker (f : A →+* B)
    (φ : S B ≅ pullback (sp (algebraMap (D K) A)) (sp (projection K)))
    (hφ : φ.hom ≫ pullback.fst _ _ = sp f) :
    Function.Surjective f ∧
      RingHom.ker f = Ideal.span ({algebraMap (D K) A (ε K)} : Set A) := by
  let ψ : S B ≅ S (A ⊗[D K] K) := φ ≪≫ pullbackSpecIso (D K) A K
  let q : op (CommRingCat.of B) ≅ op (CommRingCat.of (A ⊗[D K] K)) :=
    Scheme.Spec.preimageIso ψ
  let e : (A ⊗[D K] K) ≃+* B := q.unop.commRingCatIsoToRingEquiv
  let L : A →+* (A ⊗[D K] K) := Algebra.TensorProduct.includeLeftRingHom
  have hq : Scheme.Spec.map q.hom = ψ.hom := by
    change Scheme.Spec.map (Scheme.Spec.preimage ψ.hom) = ψ.hom
    exact Scheme.Spec.map_preimage _
  have hcat : CommRingCat.ofHom L ≫ q.unop.hom = CommRingCat.ofHom f := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change Scheme.Spec.map q.hom ≫ sp L = sp f
    rw [hq]
    change (φ.hom ≫ (pullbackSpecIso (D K) A K).hom) ≫ sp L = sp f
    rw [Category.assoc, pullbackSpecIso_hom_fst, hφ]
  apply actualReduction_surjective_ker K A f e
  intro a
  have h := congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of B => g a) hcat.symm
  change f a = e (a ⊗ₜ[D K] (1 : K)) at h
  exact h

end GeometricFibre
end SelectedSameADualNumberFibreKernel318
