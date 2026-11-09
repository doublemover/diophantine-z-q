module
public import AffineGlobalDescendedMap318
public section
noncomputable section
namespace AffineGlobalMapCoverSquare318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 3200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  {D E : OriginalSchemeDescentData318.Datum f}
  (k : OriginalSchemeDescentBaseChangeMaps318.Hom D E)

/-- The original calibrated chart square and original reconstruction
naturality give the covering square on the whole inverse-image chart. -/
lemma chart_square (U : Y.affineOpens) :
    (Scheme.Modules.pullback (AffineOriginalCoverComparison318.sourceOpen f U).ι).map
        ((Scheme.Modules.pullback f).map (AffineGlobalDescendedMap318.map f k)) ≫
      (AffineOriginalCoverCompatibility318.comparison f E U).hom =
    (AffineOriginalCoverCompatibility318.comparison f D U).hom ≫
      (Scheme.Modules.pullback (AffineOriginalCoverComparison318.sourceOpen f U).ι).map k.sheafHom := by
  let c := ActualDescentBaseChangeDiagram318.coverComparison f (f ∣_ U.1)
    (AffineOriginalCoverComparison318.sourceOpen f U).ι U.1.ι (morphismRestrict_ι f U.1).symm
  have hn := c.hom.naturality (AffineGlobalDescendedMap318.map f k)
  simp only [Functor.comp_map] at hn
  simp only [AffineOriginalCoverCompatibility318.comparison,Iso.trans_hom,Iso.app_hom,
    Functor.mapIso_hom,Category.assoc]
  rw [← Category.assoc,hn,Category.assoc,← Functor.map_comp_assoc,
    AffineGlobalDescendedMap318.pullback_square,Functor.map_comp]
  simp only [Category.assoc]
  rw [OriginalOpenChartMaps318.reconstruction_natural]

/-- The actual global descended map has the exact original covering
map under the specified globally reconstructed comparison isomorphisms. -/
lemma cover_square :
    (Scheme.Modules.pullback f).map (AffineGlobalDescendedMap318.map f k) ≫
      (AffineMorphismGlobalRecovery318.comparison f E).hom =
    (AffineMorphismGlobalRecovery318.comparison f D).hom ≫ k.sheafHom := by
  apply ModuleRestrictionCoverFaithful318.hom_ext (AffineOriginalCoverComparison318.sourceOpen f)
    (AffineOriginalCoverComparison318.cover f)
  intro U
  have hd := congrArg Iso.hom (GlobalComparisonRestriction318.pullback_iso f D U)
  have he := congrArg Iso.hom (GlobalComparisonRestriction318.pullback_iso f E U)
  simp only [Functor.mapIso_hom] at hd he
  have hh := chart_square f k U
  rw [← hd,← he] at hh
  have hp : (Scheme.Modules.pullback (AffineOriginalCoverComparison318.sourceOpen f U).ι).map
      ((Scheme.Modules.pullback f).map (AffineGlobalDescendedMap318.map f k) ≫
        (AffineMorphismGlobalRecovery318.comparison f E).hom) =
    (Scheme.Modules.pullback (AffineOriginalCoverComparison318.sourceOpen f U).ι).map
      ((AffineMorphismGlobalRecovery318.comparison f D).hom ≫ k.sheafHom) := by
    simpa only [Functor.map_comp] using hh
  let c := Scheme.Modules.restrictFunctorIsoPullback (AffineOriginalCoverComparison318.sourceOpen f U).ι
  apply (cancel_mono (c.hom.app E.line.object)).mp
  rw [c.hom.naturality,c.hom.naturality,hp]
end AffineGlobalMapCoverSquare318
