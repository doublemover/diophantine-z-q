module
public import ContactHilbertAvoidance318
public import Mathlib.AlgebraicGeometry.Cover.Open
public section
noncomputable section
namespace ContactHilbertAvoidanceAffineCover318
open AlgebraicGeometry CategoryTheory
open ContactHilbertData318
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (N : ℕ)
  (D : BoundedRank S c N)
/-- ALL affine pieces of the proved whole avoidance cover, not a chosen
coefficient localization or an assumed global source chart. -/
@[expose] def cover : (Spec S).AffineOpenCover :=
  (ContactHilbertAvoidance318.cover S c N D).affineRefinement
abbrev index := (cover S c N D).I₀
variable (i : index S c N D)
abbrev ring : CommRingCat.{0} := (cover S c N D).X i
@[expose] instance algebra : Algebra ℚ (ring S c N D i) :=
  ((Spec.preimage ((cover S c N D).f i)).hom.comp (algebraMap ℚ S)).toAlgebra
@[expose] def coefficient : S →ₐ[ℚ] ring S c N D i where
  __ := (Spec.preimage ((cover S c N D).f i)).hom
  commutes' _ := rfl
lemma coefficient_spec : Spec.map (CommRingCat.ofHom (coefficient S c N D i).toRingHom)=
    (cover S c N D).f i := Spec.map_preimage _
abbrev chart : Fin (N+1) := i.1
@[expose] def toAvoidance : Spec (ring S c N D i) ⟶
    (ContactHilbertAvoidance318.locus S c N D (chart S c N D i)).toScheme :=
  ((ContactHilbertAvoidance318.cover S c N D).X i.1).affineOpenCover.f i.2
@[reassoc] lemma avoidance_into : toAvoidance S c N D i ≫
    (ContactHilbertAvoidance318.locus S c N D (chart S c N D i)).ι=
      Spec.map (CommRingCat.ofHom (coefficient S c N D i).toRingHom) :=
  (coefficient_spec S c N D i).symm
lemma in_avoidance (x : Spec (ring S c N D i)) :
    Spec.map (CommRingCat.ofHom (coefficient S c N D i).toRingHom) x ∈
      ContactHilbertAvoidance318.locus S c N D (chart S c N D i) := by
  rw [← avoidance_into]
  exact (toAvoidance S c N D i x).property
end ContactHilbertAvoidanceAffineCover318
