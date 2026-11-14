module
public import CalibratedGlobalChartComparison318
public section
noncomputable section
namespace AffineOriginalCoverComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f) (U : Y.affineOpens)

abbrev sourceOpen : X.Opens := f ⁻¹ᵁ U.1
abbrev sourceAffine : IsAffineOpen (sourceOpen f U) := U.2.preimage f

/-- The actual restricted covering arrow agrees with the original section
map through the actual source and base affine chart isomorphisms. -/
lemma chart_square : (f ∣_ U.1) ≫ U.2.isoSpec.hom =
    (sourceAffine f U).isoSpec.hom ≫ AffineFaithfullyFlatChart318.map f U.1 := by
  apply (cancel_mono U.2.fromSpec).mp
  calc
    _ = (f ∣_ U.1) ≫ U.1.ι := by rw [Category.assoc,U.2.isoSpec_hom_fromSpec]
    _ = (sourceOpen f U).ι ≫ f := morphismRestrict_ι f U.1
    _ = ((sourceAffine f U).isoSpec.hom ≫ (sourceAffine f U).fromSpec) ≫ f :=
      congrArg (fun q => q ≫ f) (sourceAffine f U).isoSpec_hom_fromSpec.symm
    _ = _ := by
      rw [Category.assoc,AffineFaithfullyFlatChart318.square,← Category.assoc]

/-- First retain the actual inverse-image open-restriction square. -/
abbrev openPath := (PullbackChartNaturality318.chartNatIso f U.1.ι (sourceOpen f U).ι
  (f ∣_ U.1) (morphismRestrict_ι f U.1).symm).app (AffineMorphismGlobalLine318.line f D).object

/-- Then retain the exact original chart isomorphism square. -/
abbrev affinePath := (ActualDescentBaseChangeDiagram318.coverComparison U.2.isoSpec.hom
  (sourceAffine f U).isoSpec.hom (f ∣_ U.1) (AffineFaithfullyFlatChart318.map f U.1)
  (chart_square f U)).app (AffineOpenChartDescent318.line f U.1 U.2 D).object

abbrev sourcePath := (PullbackPathComposition318.iso (sourceAffine f U).isoSpec.hom
  (sourceAffine f U).fromSpec (sourceOpen f U).ι (sourceAffine f U).isoSpec_hom_fromSpec).app D.line.object

/-- On the whole original inverse image of each original affine base open,
the pullback of the constructed global line is explicitly isomorphic to the
unchanged original covering line. Every factor is an original sheaf map. -/
@[expose] def comparison :
    ((Scheme.Modules.pullback f).obj (AffineMorphismGlobalLine318.line f D).object).restrict
        (sourceOpen f U).ι ≅ D.line.object.restrict (sourceOpen f U).ι :=
  openPath f D U ≪≫
    (Scheme.Modules.pullback (f ∣_ U.1)).mapIso (CalibratedGlobalChartComparison318.comparison f D U) ≪≫
      affinePath f D U ≪≫
        (Scheme.Modules.pullback (sourceAffine f U).isoSpec.hom).mapIso
          (AffineOpenChartDescent318.comparison f U.1 U.2 D) ≪≫
            sourcePath f D U ≪≫
              ((Scheme.Modules.restrictFunctorIsoPullback (sourceOpen f U).ι).app D.line.object).symm

/-- This is a genuine full open cover of the original covering scheme,
not a list of selected source charts or a pointwise existence assertion. -/
lemma cover : (⊤ : X.Opens) ≤ iSup (sourceOpen f) :=
  LinePullbackFrames318.preimage_cover f (fun U : Y.affineOpens => U.1)
    (AffineMorphismGlobalLine318.cover (Y:=Y))

/-- Exact local original-line recovery on that full inverse-image cover.
Compatibility of these displayed maps and the global double square remain
separate proof obligations before claiming global effective descent. -/
theorem local_recovery : ∀ U : Y.affineOpens,
    Nonempty (((Scheme.Modules.pullback f).obj (AffineMorphismGlobalLine318.line f D).object).restrict
      (sourceOpen f U).ι ≅ D.line.object.restrict (sourceOpen f U).ι) :=
  fun U => ⟨comparison f D U⟩
end AffineOriginalCoverComparison318
