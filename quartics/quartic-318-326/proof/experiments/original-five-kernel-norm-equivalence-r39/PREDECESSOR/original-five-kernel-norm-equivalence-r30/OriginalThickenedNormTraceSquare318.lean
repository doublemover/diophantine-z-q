module
public import OriginalThickenedUnitSheafNorm318
public section
noncomputable section
namespace OriginalThickenedNormTraceSquare318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open DualNumberScheme318 OriginalThickenedOpenSections318
universe u
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ base R)
/-- The old actual first-projection/epsilon unit on ANY original open. -/
@[expose] def sectionUnit (V : X.Opens) (a : Γ(X,V)) : Γ(thickening R p,π R p ⁻¹ᵁ V)ˣ :=
  InfinitesimalUnitCocycle318.unit (thickening R p)
    (DualNumberInfinitesimalLines318.epsilon R p)
    (DualNumberInfinitesimalLines318.epsilon_square R p)
    (π R p ⁻¹ᵁ V) ((π R p).app V a)
lemma sectionUnit_affine (V : X.Opens) [IsAffine V.toScheme] (a : Γ(X,V)) :
    sectionUnit R p V a = OriginalOpenUnitLogarithm318.exp R p V a :=
  (OriginalOpenUnitLogarithm318.exp_original R p V a).symm
lemma sectionUnit_restrict {V W : X.Opens} (h : W ≤ V) (a : Γ(X,V)) :
    Units.map ((thickening R p).presheaf.map (homOfLE ((π R p).preimage_mono h)).op).hom.toMonoidHom
      (sectionUnit R p V a) = sectionUnit R p W (X.presheaf.map (homOfLE h).op a) := by
  dsimp only [sectionUnit]
  rw [InfinitesimalUnitCocycle318.unit_restrict]
  congr 1
  exact (congrArg (fun k => k a) ((π R p).naturality (homOfLE h).op)).symm
variable {Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (q : Y ⟶ base R) (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (hY : NormalAffineBasis318.HasBasis Y)
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
/-- The genuine whole unit-sheaf norm has the OLD trace as its first-order
map on EVERY original open, including non-affine and empty intersections.
The norm was independently constructed on all units and identified with local
determinants before this epsilon square is proved by actual sheaf separation. -/
lemma norm_sectionUnit (U : Y.Opens) (a : Γ(X,f ⁻¹ᵁ U)) :
    (OriginalThickenedUnitSheafNorm318.norm R p q f hY hfinite).hom.app (op U)
      (sectionUnit R p (f ⁻¹ᵁ U) a) =
    sectionUnit R q U (OpenDominantTrace318.trace f hY hfinite U a) := by
  apply TopCat.Presheaf.IsSheaf.section_ext (OriginalThickenedUnitSheafNorm318.target R q).property
  intro y hy
  obtain ⟨_,⟨V,hV,rfl⟩,hyV,hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
  refine ⟨V,hVU,hyV,?_⟩
  change Units.map ((thickening R q).presheaf.map (homOfLE ((π R q).preimage_mono hVU)).op).hom.toMonoidHom
      ((OriginalThickenedUnitSheafNorm318.norm R p q f hY hfinite).hom.app (op U)
        (sectionUnit R p (f ⁻¹ᵁ U) a)) =
    Units.map ((thickening R q).presheaf.map (homOfLE ((π R q).preimage_mono hVU)).op).hom.toMonoidHom
      (sectionUnit R q U (OpenDominantTrace318.trace f hY hfinite U a))
  rw [OriginalThickenedUnitSheafNorm318.restrict, sectionUnit_restrict, sectionUnit_restrict,
    OpenDominantTrace318.restrict f hY hfinite (homOfLE hVU),
    OriginalThickenedUnitSheafNorm318.affine_value R p q f hY hfinite V hV]
  letI : IsAffine V.toScheme := hV
  letI : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  rw [sectionUnit_affine, sectionUnit_affine,
    ActualThickenedAffineUnitNorm318.infinitesimal_value]
end OriginalThickenedNormTraceSquare318
