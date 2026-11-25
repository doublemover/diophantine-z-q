module
public import OriginalR47ReesChartMapValues318
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Basic
public section
noncomputable section

namespace OriginalR47ReesChartTensor318

open OriginalAffineReesBlowup318
open OriginalAffineReesChartLocal318 OriginalR47ReesLiteralFractions318
open OriginalR47ReesChartMapValues318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) (a : A) (ha : a ∈ I)

local notation "f" => algebraMap A B
local notation "C" => chart I a ha
local notation "D" => newChart I (algebraMap A B) a ha
local notation "aB" => algebraMap A B a
local notation "Aa" => Localization.Away a
local notation "Ba" => Localization.Away (algebraMap A B a)

instance oldAlgebra : Algebra A C := (chartScalars I a ha).toAlgebra
instance newAlgebra : Algebra B D :=
  (chartScalars (I.map f) aB (newHa I f a ha)).toAlgebra
instance newOldAlgebra : Algebra A D :=
  ((chartScalars (I.map f) aB (newHa I f a ha)).comp f).toAlgebra

@[expose] def cToD : C →ₐ[A] D where
  __ := chartHom I f a ha
  commutes' := chart_scalar I f a ha

/-- R-algebra tensor universal map, before changing its scalar
label to B. This pins actual structural B scalars through the chosen
coefficient map and avoids a second inferred homogeneous-localization
SMul. -/
@[expose] def bToD : B →ₐ[A] D :=
  ⟨chartScalars (I.map f) aB (newHa I f a ha), fun _ => rfl⟩

@[expose] def compareR : B ⊗[A] C →ₐ[A] D :=
  Algebra.TensorProduct.productMap (bToD I a ha) (cToD I a ha)

/-- This is the specified affine tensor map, not a chosen isomorphism. -/
@[expose] def compare : B ⊗[A] C →ₐ[B] D where
  toRingHom := (compareR I a ha).toRingHom
  commutes' b := by
    change compareR I a ha (b ⊗ₜ[A] (1 : C)) = (bToD I a ha) b
    exact Algebra.TensorProduct.productMap_left_apply (bToD (B:=B) I a ha) (cToD (B:=B) I a ha) b

theorem compare_tmul (b : B) (z : C) :
    compare I a ha (b ⊗ₜ[A] z) =
      chartScalars (I.map f) aB (newHa I f a ha) b * chartHom I f a ha z :=
  Algebra.TensorProduct.productMap_apply_tmul (bToD (B:=B) I a ha) (cToD (B:=B) I a ha) b z

/-- The exact localization of the tensor by the localized old
denominator, using the pinned stock tensor-localization theorem. -/
@[expose] def ambientCompare : B ⊗[A] Aa ≃ₐ[B] Ba :=
  IsLocalization.Away.tensorEquiv (A:=Aa) (r:=a) B

/-- The right leg is the original `ambient f a`, by localization
uniqueness on the exact old coefficient map. No extra A_a scalar
action on the target localization is synthesized. -/
theorem ambientCompare_right (z : Aa) :
    ambientCompare (B:=B) a ((1 : B) ⊗ₜ[A] z) = ambient f a z := by
  let i : Aa →ₐ[A] B ⊗[A] Aa := Algebra.TensorProduct.includeRight
  let g : Aa →+* Ba := (ambientCompare (B:=B) a).toRingEquiv.toRingHom.comp i.toRingHom
  have h : g = ambient f a := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    apply RingHom.ext
    intro x
    change ambientCompare (B:=B) a ((1 : B) ⊗ₜ[A] algebraMap A Aa x) =
      ambient f a (algebraMap A Aa x)
    have ht : ((1 : B) ⊗ₜ[A] algebraMap A Aa x) =
        algebraMap B (B ⊗[A] Aa) (f x) := by
      change i (algebraMap A Aa x) = _
      rw [i.commutes, IsScalarTower.algebraMap_apply A B (B ⊗[A] Aa)]
    rw [ht,(ambientCompare (B:=B) a).commutes]
    have hA : (⟨a^0,0,rfl⟩ : Submonoid.powers a) = 1 :=
      Subtype.ext (pow_zero a)
    have hB : (⟨aB^0,0,rfl⟩ : Submonoid.powers aB) = 1 :=
      Subtype.ext (pow_zero aB)
    simpa only [hA,hB,IsLocalization.mk'_one] using (ambient_ratio f a 0 x).symm
  exact RingHom.congr_fun h z

theorem ambientCompare_tmul (b : B) (z : Aa) :
    ambientCompare (B:=B) a (b ⊗ₜ[A] z) = algebraMap B Ba b * ambient f a z := by
  have ht : b ⊗ₜ[A] z =
      (algebraMap B (B ⊗[A] Aa) b) * ((1 : B) ⊗ₜ[A] z) := by
    change b ⊗ₜ[A] z = (b ⊗ₜ[A] (1 : Aa)) * ((1 : B) ⊗ₜ[A] z)
    rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  rw [ht,map_mul,(ambientCompare (B:=B) a).commutes,ambientCompare_right]

@[expose] def oldEval : C →ₐ[A] Aa where
  __ := chartEval I a ha
  commutes' := chartEval_scalar I a ha

@[expose] def newEval : D →ₐ[B] Ba where
  toRingHom := chartEval (I.map f) aB (newHa I f a ha)
  commutes' b := by
    change chartEval (I.map f) aB (newHa I f a ha)
      (chartScalars (I.map f) aB (newHa I f a ha) b) = algebraMap B Ba b
    exact chartEval_scalar (I.map f) aB (newHa I f a ha) b

@[expose] def flatMap : B ⊗[A] C →ₐ[B] B ⊗[A] Aa :=
  Algebra.TensorProduct.map (AlgHom.id B B) (oldEval I a ha)

theorem flatMap_tmul (b : B) (z : C) :
    flatMap I a ha (b ⊗ₜ[A] z) = b ⊗ₜ[A] oldEval I a ha z :=
  rfl

theorem compare_into_ambient (z : B ⊗[A] C) :
    newEval (B:=B) I a ha (compare (B:=B) I a ha z) =
      ambientCompare (B:=B) a (flatMap (B:=B) I a ha z) := by
  have h : (newEval (B:=B) I a ha).comp (compare (B:=B) I a ha) =
      (ambientCompare (B:=B) a).toAlgHom.comp (flatMap (B:=B) I a ha) := by
    apply Algebra.TensorProduct.ext'
    intro b w
    change newEval (B:=B) I a ha (compare I a ha (b ⊗ₜ[A] w)) =
      ambientCompare (B:=B) a (flatMap I a ha (b ⊗ₜ[A] w))
    rw [compare_tmul, flatMap_tmul, ambientCompare_tmul]
    change chartEval (I.map f) aB (newHa I f a ha)
        (chartScalars (I.map f) aB (newHa I f a ha) b * chartHom I f a ha w) =
      algebraMap B Ba b * ambient f a (chartEval I a ha w)
    rw [(chartEval (I.map f) aB (newHa I f a ha)).map_mul, chartEval_scalar, chart_ambient]
  exact DFunLike.congr_fun h z

/-- Injectivity from genuine flatness into the true ambient coefficient
localization. This never uses an étale ring being a domain. -/
theorem compare_injective [Module.Flat A B] :
    Function.Injective (compare (B:=B) I a ha) := by
  let L := (oldEval I a ha).toLinearMap.lTensor B
  have hL : Function.Injective L :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      (chartEval_injective I a ha)
  have hread : L = ((flatMap (B:=B) I a ha).restrictScalars A).toLinearMap :=
    TensorProduct.ext' (fun _ _ => rfl)
  intro x y h
  apply hL
  apply (ambientCompare (B:=B) a).injective
  rw [show L x = flatMap (B:=B) I a ha x from DFunLike.congr_fun hread x,
    show L y = flatMap (B:=B) I a ha y from DFunLike.congr_fun hread y,
    ← compare_into_ambient I a ha x, ← compare_into_ambient I a ha y, h]

end OriginalR47ReesChartTensor318

#print axioms OriginalR47ReesChartTensor318.ambientCompare_right
#print axioms OriginalR47ReesChartTensor318.ambientCompare_tmul
#print axioms OriginalR47ReesChartTensor318.compare_tmul
#print axioms OriginalR47ReesChartTensor318.compare_into_ambient
#print axioms OriginalR47ReesChartTensor318.compare_injective
