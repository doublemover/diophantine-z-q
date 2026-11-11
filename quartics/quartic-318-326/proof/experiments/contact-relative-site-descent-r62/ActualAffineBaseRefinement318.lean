module
public import RefinedCoverCategoricalEquivalence318
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public section
noncomputable section
namespace ActualAffineBaseRefinement318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A specified genuine affine faithfully flat refinement, retaining its
original source, map to the original cover and exact factorization. -/
structure Refinement where
  source : Scheme.{u}
  map : source ⟶ Y
  lift : source ⟶ X
  affine : IsAffineHom map
  flat : Flat map
  surjective : Surjective map
  factor : lift ≫ f = map
attribute [instance] Refinement.affine Refinement.flat Refinement.surjective

variable [Flat f] [Surjective f]
abbrev cover : Scheme.Cover.{u} (Scheme.precoverage @Flat) Y := f.cover (inferInstance : Flat f)

/-- On an affine base, a quasi-compact flat covering family has a finite
original affine refinement. Its finite disjoint union is the required
single affine faithfully flat cover factoring through the original f. -/
lemma exists_refinement [IsAffine Y] [QuasiCompactCover (cover f).toPreZeroHypercover] :
    Nonempty (Refinement f) := by
  have he : ∃ (V : Scheme.AffineCover.{u} @Flat Y) (r : V.cover ⟶ cover f),
      Finite V.I₀ ∧ ∀ i, IsOpenImmersion (r.h₀ i) := QuasiCompactCover.exists_hom (cover f)
  obtain ⟨V,r,hfin,ho⟩ := he
  letI : Finite V.I₀ := hfin
  let W : Scheme.{u} := ∐ V.cover.X
  let b : W ⟶ Y := Sigma.desc V.cover.f
  let c : W ⟶ X := Sigma.desc (fun i => r.h₀ i)
  haveI : IsAffine W := by dsimp [W]; infer_instance
  have hb : Flat b := V.cover.sigma.map_prop default
  have hs : Surjective b := inferInstanceAs (Surjective (Sigma.desc V.cover.f))
  have hc : c ≫ f = b := by
    apply Sigma.hom_ext
    intro i
    simpa only [c,b,Category.assoc,Sigma.ι_desc] using r.w₀ i
  exact ⟨{ source := W, map := b, lift := c,
    affine := inferInstance, flat := hb, surjective := hs, factor := hc }⟩

@[expose] def refinement [IsAffine Y] [QuasiCompactCover (cover f).toPreZeroHypercover] :
    Refinement f := Classical.choice (exists_refinement f)
end ActualAffineBaseRefinement318
