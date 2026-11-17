module
public import ActualTwoDescentOpenChartAmbientCoordinates318
public section
noncomputable section
namespace ActualTwoDescentOpenChartCoordinateNaturality318
open CategoryTheory AlgebraicGeometry Opposite
open ActualTwoDescentOpenChartAmbientCoordinates318
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf)

lemma coordinate_natural (V W : X.Opens) (hV : V≤j.opensRange) (hW : W≤V) (s : Γ(M,V)) :
    X.presheaf.map (homOfLE hW).op (coordinate j M f V hV s)=
      coordinate j M f W (hW.trans hV) (M.presheaf.map (homOfLE hW).op s) := by
  apply (ConcreteCategory.bijective_of_isIso (ambientRingIso j W (hW.trans hV)).hom).injective
  rw [ambientRingIso_hom,coordinate_structure]
  have hr := congrArg (fun z => z (coordinate j M f V hV s))
    ((StructurePushforwardSplit318.unitMap j).mapPresheaf.naturality (homOfLE hW).op)
  have hf := congrArg (fun z => z s)
    ((adjoint j M f).mapPresheaf.naturality (homOfLE hW).op)
  change j.app W (X.presheaf.map (homOfLE hW).op (coordinate j M f V hV s))=
    ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit Y.ringCatSheaf)).presheaf.map (homOfLE hW).op
      (j.app V (coordinate j M f V hV s)) at hr
  rw [coordinate_structure] at hr
  exact hr.trans hf.symm

/-- On a full chart image the adjunction unit is restriction along an
EQUALITY of opens. Hence an actual chart isomorphism is bijective on every
ambient subopen,not merely on stalks or on global sections. -/
lemma coordinate_bijective [IsIso f] (V : X.Opens) (hV : V≤j.opensRange) :
    Function.Bijective (coordinate j M f V hV) := by
  have hi := ConcreteCategory.bijective_of_isIso
    (M.presheaf.mapIso (eqToIso (image_preimage j V hV)).op).hom
  have hf := ConcreteCategory.bijective_of_isIso (f.app (j⁻¹ᵁ V))
  have ha : Function.Bijective ((adjoint j M f).app V) := by
    change Function.Bijective (((Scheme.Modules.restrictAdjunction j).homEquiv _ _ f).app V)
    rw [Adjunction.homEquiv_unit]
    change Function.Bijective (fun s => f.app (j⁻¹ᵁ V)
      (M.presheaf.map (homOfLE (j.image_preimage_le V)).op s))
    exact hf.comp hi
  exact (ConcreteCategory.bijective_of_isIso (ambientRingIso j V hV).inv).comp ha
end ActualTwoDescentOpenChartCoordinateNaturality318
