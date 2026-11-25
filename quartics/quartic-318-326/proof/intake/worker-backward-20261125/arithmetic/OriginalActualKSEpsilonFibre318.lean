module
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
The literal affine central fibre in the fixed (T+epsilon) deformation.
The ring homomorphism is the first projection of the actual Scheme
pullback, not a supplied surjection or an independently chosen ring.
-/
@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open TrivSqZeroExt

namespace OriginalActualKSEpsilonFibre318

universe u

abbrev Sq (K : Type u) := TrivSqZeroExt K K
def epsilon (K : Type u) [CommRing K] : Sq K := inr (1 : K)

variable (K : Type u) [CommRing K]

local instance : Algebra (Sq K) K := TrivSqZeroExt.algebraBase K K

theorem base_ker : RingHom.ker (algebraMap (Sq K) K) =
    Ideal.span ({epsilon K} : Set (Sq K)) := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change x.fst=0 ↔ epsilon K ∣ x
  constructor
  · intro hx
    refine ⟨inl x.snd,?_⟩
    rw [epsilon,inr_mul_inl,op_smul_eq_smul,smul_eq_mul,mul_one]
    apply TrivSqZeroExt.ext
    · simpa only [fst_inr] using hx
    · simp
  · rintro ⟨y,rfl⟩
    simp [epsilon]

def baseQuot :
    (Sq K ⧸ RingHom.ker (algebraMap (Sq K) K)) ≃ₐ[Sq K] K :=
  Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId (Sq K) K) (by
    intro k
    exact ⟨inl k,rfl⟩)

variable (B : Type u) [CommRing B] [Algebra (Sq K) B]

abbrev reduction : B →+* B ⊗[Sq K] K := algebraMap B (B ⊗[Sq K] K)

def fibreIdeal : Ideal B := (RingHom.ker (algebraMap (Sq K) K)).map (algebraMap (Sq K) B)

theorem fibreIdeal_eq : fibreIdeal K B =
    Ideal.span ({algebraMap (Sq K) B (epsilon K)} : Set B) := by
  rw [fibreIdeal,base_ker,Ideal.map_span,Set.image_singleton]

/-- Ordinary tensor base change produces the quotient by the one
structural epsilon of the scheme, without flatness or a chart splitting. -/
def affineCentralFibre : (B ⧸ fibreIdeal K B) ≃ₐ[B] B ⊗[Sq K] K :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (RingHom.ker (algebraMap (Sq K) K))).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) (baseQuot K))

theorem projection_read (b : B) :
    affineCentralFibre K B (Ideal.Quotient.mk _ b) = reduction K B b := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rw [affineCentralFibre,AlgEquiv.trans_apply,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul] <;> simp

theorem projection_ker :
    RingHom.ker (reduction K B) =
      Ideal.span ({algebraMap (Sq K) B (epsilon K)} : Set B) := by
  rw [← fibreIdeal_eq]
  ext b
  rw [RingHom.mem_ker, ← projection_read]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    apply (affineCentralFibre K B).injective
    rw [h,map_zero]
  · intro h
    rw [h,map_zero]

theorem projection_surj : Function.Surjective (reduction K B) := by
  intro t
  obtain ⟨a,ha⟩ := (affineCentralFibre K B).surjective t
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨b,(projection_read K B b).symm.trans ha⟩

/-- The actual Scheme pullback of this affine original open along ε=0. -/
abbrev actualPull :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap (Sq K) B)))
    (Spec.map (CommRingCat.ofHom (algebraMap (Sq K) K)))

def actualFibreChart : Spec (.of (B ⧸ fibreIdeal K B)) ≅ actualPull K B :=
  Scheme.Spec.mapIso (affineCentralFibre K B).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso (Sq K) B K).symm

theorem actual_fst :
    (actualFibreChart K B).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (fibreIdeal K B))) := by
  change (Scheme.Spec.mapIso
    (affineCentralFibre K B).symm.toRingEquiv.toCommRingCatIso.op).hom ≫
    ((pullbackSpecIso (Sq K) B K).inv ≫ pullback.fst _ _) = _
  rw [pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom (affineCentralFibre K B).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (reduction K B)) = _
  have e : CommRingCat.ofHom (reduction K B) ≫
      CommRingCat.ofHom (affineCentralFibre K B).symm.toRingHom =
        CommRingCat.ofHom (Ideal.Quotient.mk (fibreIdeal K B)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change (affineCentralFibre K B).symm (reduction K B b) = _
    rw [← projection_read,AlgEquiv.symm_apply_apply]
  rw [← Spec.map_comp,e]

end OriginalActualKSEpsilonFibre318

#print axioms OriginalActualKSEpsilonFibre318.base_ker
#print axioms OriginalActualKSEpsilonFibre318.projection_ker
#print axioms OriginalActualKSEpsilonFibre318.projection_surj
#print axioms OriginalActualKSEpsilonFibre318.actual_fst
