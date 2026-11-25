module
public import OriginalR47ReesChartTensor318
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.Constructions
public section
noncomputable section

namespace OriginalR47ReesAffinePushout318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalAffineReesBlowup318 OriginalAffineReesChartLocal318
open OriginalR47ReesLiteralFractions318 OriginalR47ReesChartMapValues318
open OriginalR47ReesChartTensor318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) (a : A) (ha : a ∈ I)

local notation "f" => algebraMap A B
local notation "C" => chart I a ha
local notation "D" => newChart I (algebraMap A B) a ha
local notation "aB" => algebraMap A B a
local notation "Ba" => Localization.Away (algebraMap A B a)

/-- In the full coefficient localization use one fixed denominator to
linearly read the possible numerators of actual target Proj fractions. -/
@[expose] def oneDenominator (n : ℕ) : B →ₗ[B] Ba :=
  (LinearMap.mulRight B
    (IsLocalization.mk' Ba 1 (⟨aB^n,n,rfl⟩ : Submonoid.powers aB))).comp
    (Algebra.linearMap B Ba)

theorem oneDenominator_read (n : ℕ) (r : B) :
    oneDenominator a n r =
      IsLocalization.mk' Ba r (⟨aB^n,n,rfl⟩ : Submonoid.powers aB) := by
  rw [oneDenominator, LinearMap.comp_apply, LinearMap.mulRight_apply, Algebra.linearMap_apply]
  exact (IsLocalization.mk'_eq_mul_mk'_one (S:=Ba) r
    (⟨aB^n,n,rfl⟩ : Submonoid.powers aB)).symm

/-- Surjectivity is proved by the image ideal of I^n on this chart:
each generator f(r) in its span comes from 1 ⊗ (rT^n/(aT)^n).
No flatness is required for this half. -/
theorem compare_surjective : Function.Surjective (compare I a ha : B ⊗[A] C →ₐ[B] D) := by
  let E : B ⊗[A] C →ₐ[B] Ba := (newEval I a ha).comp (compare I a ha)
  let M : Submodule B Ba := E.toLinearMap.range
  intro z
  obtain ⟨n,r,hr⟩ := exists_ratio (I.map f) aB (newHa I f a ha) z
  have hI : Ideal.map f (I^n) ≤ M.comap (oneDenominator a n) := by
    change Submodule.span B (f '' ((I^n : Ideal A) : Set A)) ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨c,hc,rfl⟩
    change oneDenominator a n (f c) ∈ M
    refine ⟨(1:B) ⊗ₜ[A] ratio I a ha n ⟨c,hc⟩, ?_⟩
    change newEval I a ha (compare I a ha ((1:B) ⊗ₜ[A] ratio I a ha n ⟨c,hc⟩)) =
      oneDenominator a n (f c)
    rw [compare_tmul, (chartScalars (I.map f) aB (newHa I f a ha)).map_one,
      one_mul]
    change chartEval (I.map f) aB (newHa I f a ha)
        (chartHom I f a ha (ratio I a ha n ⟨c,hc⟩)) =
      oneDenominator a n (f c)
    rw [chart_ambient, chartEval_ratio, ambient_ratio, oneDenominator_read]
  have hmem : r.val ∈ Ideal.map f (I^n) := by
    rw [Ideal.map_pow]
    exact r.property
  have hm := hI hmem
  change oneDenominator a n r.val ∈ M at hm
  obtain ⟨x,hx⟩ := hm
  refine ⟨x, chartEval_injective (I.map f) aB (newHa I f a ha) ?_⟩
  change newEval I a ha (compare I a ha x) = chartEval (I.map f) aB (newHa I f a ha) z
  rw [← hr, chartEval_ratio]
  exact hx.trans (oneDenominator_read a n r.val)

@[expose] def comparison [Module.Flat A B] : B ⊗[A] C ≃ₐ[B] D :=
  AlgEquiv.ofBijective (compare I a ha)
    ⟨compare_injective I a ha, compare_surjective I a ha⟩

/-- The true comparison supplies the exact four original coefficient
maps. Pushout transport is done in CommRingCat, so the heterogeneous
actions on the target homogeneous localization are not reconstructed. -/
theorem ring_pushout [Module.Flat A B] :
    IsPushout (CommRingCat.ofHom f)
      (CommRingCat.ofHom (chartScalars I a ha))
      (CommRingCat.ofHom (chartScalars (I.map f) aB (newHa I f a ha)))
      (CommRingCat.ofHom (chartHom I f a ha)) := by
  let E := (comparison (B:=B) I a ha).toRingEquiv.toCommRingCatIso
  refine (CommRingCat.isPushout_tensorProduct A B C).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) E (by simp) ?_ ?_ ?_
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    change algebraMap A C t = chartScalars I a ha t
    apply chartEval_injective I a ha
    rw [chartEval_scalar]
    exact (oldEval I a ha).commutes t
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change compare (B:=B) I a ha (b ⊗ₜ[A] (1:C)) =
      chartScalars (I.map f) aB (newHa I f a ha) b
    rw [compare_tmul, (chartHom I f a ha).map_one]
    exact mul_one ((chartScalars (I.map f) aB (newHa I f a ha)) b)
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change compare (B:=B) I a ha ((1:B) ⊗ₜ[A] z) = chartHom I f a ha z
    rw [compare_tmul, (chartScalars (I.map f) aB (newHa I f a ha)).map_one]
    exact one_mul ((chartHom I f a ha) z)

/-- Literal Cartesian square of both original affine Proj charts.
This is a square of genuine Schemes and not just a ring comparison. -/
theorem affine_pullback [Module.Flat A B] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (chartScalars (I.map f) aB (newHa I f a ha))))
      (Spec.map (CommRingCat.ofHom (chartHom I f a ha)))
      (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom (chartScalars I a ha))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (ring_pushout (B:=B) I a ha)

end OriginalR47ReesAffinePushout318

#print axioms OriginalR47ReesAffinePushout318.compare_surjective
#print axioms OriginalR47ReesAffinePushout318.comparison
#print axioms OriginalR47ReesAffinePushout318.ring_pushout
#print axioms OriginalR47ReesAffinePushout318.affine_pullback
