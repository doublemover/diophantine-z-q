module
public import ActualMulAffineEtale318
public import Mathlib.AlgebraicGeometry.Gluing
import all WeierstrassGluing318
public section
noncomputable section

namespace ActualMulGlobalEtale318
open AlgebraicGeometry CategoryTheory
open SelectedLiteralTorsionKernel318 ActualNonSplitIdentityLifts318
open ActualMulAffineEtale318

variable (n m : ℕ)
local notation "R₀" => OpenJModel318.Base n

/-- Pull back the actual target affine cover along [m], then take the
actual affine cover of each such open preimage. Each chart pair is
therefore a restriction of the same actual multiplication morphism. -/
theorem mul_etale (hm : IsUnit (m : R₀)) : Etale (mulMap n m) := by
  let U := (Curve n).affineOpenCover
  let V : (Curve n).OpenCover := U.openCover.pullback₁ (mulMap n m)
  letI : HasAffineProperty (@Etale) (sourceAffineLocally (@RingHom.Etale)) :=
    HasRingHomProperty.HasAffineProperty (P := @Etale) (Q := @RingHom.Etale)
  letI : ∀ a, IsAffine (U.openCover.X a) := fun a =>
    inferInstanceAs (IsAffine (Spec (U.X a)))
  refine HasAffineProperty.of_openCover (P := @Etale)
    (Q := sourceAffineLocally (@RingHom.Etale)) U.openCover ?_
  intro a
  let g : V.X a ⟶ Spec (U.X a) := U.openCover.pullbackHom (mulMap n m) a
  let W := (V.X a).affineOpenCover
  letI : IsAffine (Spec (U.X a)) := inferInstance
  refine (HasAffineProperty.iff_of_isAffine (P := @Etale)
    (Q := sourceAffineLocally (@RingHom.Etale)) (f := g)).mp ?_
  letI : ∀ b, IsAffine (W.openCover.X b) := fun b =>
    inferInstanceAs (IsAffine (Spec (W.X b)))
  refine HasRingHomProperty.of_source_openCover (P := @Etale) (Q := @RingHom.Etale)
    (f := g) W.openCover ?_
  intro b
  let i : Spec (W.X b) ⟶ Curve n := W.f b ≫ V.f a
  let j : Spec (U.X a) ⟶ Curve n := U.f a
  let φ : Spec (W.X b) ⟶ Spec (U.X a) :=
    W.f b ≫ U.openCover.pullbackHom (mulMap n m) a
  letI : IsOpenImmersion i :=
    inferInstanceAs (IsOpenImmersion (W.openCover.f b ≫ V.f a))
  letI : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (U.openCover.f a))
  have hcomm : φ ≫ j = i ≫ mulMap n m := by
    change (W.f b ≫ U.openCover.pullbackHom (mulMap n m) a) ≫ U.openCover.f a =
      (W.f b ≫ (U.openCover.pullback₁ (mulMap n m)).f a) ≫ mulMap n m
    simpa only [Category.assoc] using
      congrArg (fun t => W.f b ≫ t) (U.openCover.pullbackHom_map (mulMap n m) a)
  have hmem : Set.range (i ≫ mulMap n m) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    refine ⟨φ x, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun t : Spec (W.X b) ⟶ Curve n => t x) hcomm
  obtain ⟨aMap, ha⟩ := Spec.map_surjective (i ≫ projection n)
  obtain ⟨bMap, hb⟩ := Spec.map_surjective (j ≫ projection n)
  letI : Algebra R₀ (W.X b) := aMap.hom.toAlgebra
  letI : Algebra R₀ (U.X a) := bMap.hom.toAlgebra
  have hi : i ≫ projection n = baseFor n (W.X b) := ha.symm
  have hj : j ≫ projection n = baseFor n (U.X a) := hb.symm
  obtain ⟨k, hk, he⟩ := exists_etale_mul_restriction n i j hi hj m hm hmem
  haveI : Etale (specOf n k) := he
  haveI : Etale (φ ≫ j) := by
    rw [hcomm,hk]
    infer_instance
  have hφ : Etale φ := Etale.of_comp φ j
  change (φ.appTop).hom.Etale
  exact HasRingHomProperty.appTop (@Etale) φ hφ

end ActualMulGlobalEtale318
