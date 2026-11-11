module
public import AffineBasisUnitMaps318
public section
noncomputable section
namespace OriginalThickenedUnitSheafNorm318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 OriginalThickenedOpenSections318
universe u
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ base R) (q : Y ⟶ base R) (f : X ⟶ Y)
/-- Actual nonreduced source units, pushed along the ORIGINAL projection and
original map. Every component is the entire original inverse-image open. -/
@[expose] def source : TopCat.Sheaf CommGrpCat.{u} Y.carrier :=
  ⟨(f.base _* ((π R p).base _* (thickening R p).presheaf)) ⋙ OpenUnitNorm318.unitsFunctor,
    StructureUnitsSheaf318.isSheaf
      ⟨f.base _* ((π R p).base _* (thickening R p).presheaf),
        TopCat.Sheaf.pushforward_sheaf_of_sheaf f.base
          (TopCat.Sheaf.pushforward_sheaf_of_sheaf (π R p).base (thickening R p).sheaf.property)⟩⟩
@[expose] def target : TopCat.Sheaf CommGrpCat.{u} Y.carrier :=
  StructureUnitsSheaf318.pushedUnits (π R q)
variable [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsFinite f]
    (hY : NormalAffineBasis318.HasBasis Y)
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
@[expose] def affineData : AffineBasisUnitMaps318.Data (source R p f).obj (target R q) where
  app U := ActualThickenedAffineUnitNorm318.norm R p q f hY hfinite U.1 U.2
  natural U V h z := ActualThickenedAffineUnitNorm318.restrict R p q f hY hfinite U.2 V.2 h z
/-- A genuine morphism of ACTUAL nonreduced unit sheaves on the original base
space. It extends the old norm on coefficient units and has the original trace
as first-order coefficient. No integrality of the thickening is required. -/
@[expose] def norm : source R p f ⟶ target R q :=
  ⟨AffineBasisUnitMaps318.extend (affineData R p q f hY hfinite)⟩
lemma affine_value (U : Y.Opens) (hU : IsAffineOpen U)
    (z : Γ(thickening R p,π R p ⁻¹ᵁ (f ⁻¹ᵁ U))ˣ) :
    (norm R p q f hY hfinite).hom.app (op U) z =
      ActualThickenedAffineUnitNorm318.norm R p q f hY hfinite U hU z :=
  congrArg (fun k => k z)
    (AffineBasisUnitMaps318.extend_affine (affineData R p q f hY hfinite) ⟨U,hU⟩)
/-- The genuine morphism respects ALL old-open restrictions, including those
whose endpoints or intersections are non-affine or empty. -/
lemma restrict {U V : Y.Opens} (h : V ≤ U)
    (z : Γ(thickening R p,π R p ⁻¹ᵁ (f ⁻¹ᵁ U))ˣ) :
    Units.map ((thickening R q).presheaf.map (homOfLE ((π R q).preimage_mono h)).op).hom.toMonoidHom
      ((norm R p q f hY hfinite).hom.app (op U) z) =
    (norm R p q f hY hfinite).hom.app (op V)
      (Units.map ((thickening R p).presheaf.map
        (homOfLE ((π R p).preimage_mono (f.preimage_mono h))).op).hom.toMonoidHom z) :=
  (congrArg (fun k => k z) ((norm R p q f hY hfinite).hom.naturality (homOfLE h).op)).symm
/-- Every actual nonreduced unit is controlled by the ORIGINAL determinant
norm on any original finite-free affine neighborhood. -/
lemma determinant_agreement (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bs : letI := (f.app U).hom.toAlgebra
      Module.Basis ι Γ(Y,U) Γ(X,f ⁻¹ᵁ U))
    (z : Γ(thickening R p,π R p ⁻¹ᵁ (f ⁻¹ᵁ U))ˣ) :
    letI := (f.app U).hom.toAlgebra
    letI := OriginalDualAlgebraNormTrace318.actualAlgebra Γ(Y,U) Γ(X,f ⁻¹ᵁ U)
    letI : IsAffine U.toScheme := hU
    letI : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
    (norm R p q f hY hfinite).hom.app (op U) z = OriginalOpenDualCoordinates318.units R q U
      (Units.map (Algebra.norm (DualNumber Γ(Y,U)))
        (OriginalOpenDualCoordinates318.inverseUnits R p (f ⁻¹ᵁ U) z)) := by
  rw [affine_value R p q f hY hfinite U hU]
  exact ActualThickenedAffineUnitNorm318.determinant_agreement R p q f hY hfinite U hU bs z
/-- Actual unit cocycles and actual changes of frame on arbitrary full covers
are transported by the same global nonreduced sheaf morphism. -/
@[expose] def mapCocycle {ι : Type u} (U : ι → Y.Opens)
    (c : UnitTransitionCocycle318.Cocycle (source R p f).obj U) :
    UnitTransitionCocycle318.Cocycle (target R q).obj U :=
  UnitTransitionCocycle318.map (norm R p q f hY hfinite).hom c
lemma map_gauge {ι : Type u} (U : ι → Y.Opens)
    (c d : UnitTransitionCocycle318.Cocycle (source R p f).obj U)
    (h : UnitTransitionCocycle318.GaugeEquivalent c d) :
    UnitTransitionCocycle318.GaugeEquivalent
      (mapCocycle R p q f hY hfinite U c) (mapCocycle R p q f hY hfinite U d) :=
  UnitTransitionCocycle318.map_gaugeEquivalent (norm R p q f hY hfinite).hom h
end OriginalThickenedUnitSheafNorm318
