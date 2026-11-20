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
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale) V
  intro a
  let W := (V.X a).affineOpenCover
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale) W.openCover
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
  change Etale (W.f b ≫ (V.f a ≫ mulMap n m))
  rw [← Category.assoc]
  change Etale (i ≫ mulMap n m)
  rw [hk]
  infer_instance

end ActualMulGlobalEtale318
