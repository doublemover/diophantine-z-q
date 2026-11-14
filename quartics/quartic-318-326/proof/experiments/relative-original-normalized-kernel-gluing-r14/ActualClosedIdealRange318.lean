module
public import ActualClosedIdealModule318
public section
noncomputable section
namespace ActualClosedIdealRange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) (V : X.Opens)
local notation "E" => SheafOfModules.evaluation X.ringCatSheaf (op V)
lemma range_eq : LinearMap.range (E.map (ActualClosedIdealModule318.inclusion p)).hom=
    LinearMap.ker (E.map (ActualClosedIdealModule318.structure p)).hom := by
  ext a
  constructor
  · rintro ⟨s,rfl⟩
    have h := congrArg (fun k => k.app V s) (ActualClosedIdealModule318.inclusion_structure p)
    exact h
  · intro ha
    refine ⟨(ActualClosedIdealModule318.sectionsIso p V).inv ⟨a,ha⟩,?_⟩
    exact congrArg (fun k => k (⟨a,ha⟩ : LinearMap.ker
      (E.map (ActualClosedIdealModule318.structure p)).hom))
        (ActualClosedIdealModule318.sectionsIso_inv_inclusion p V)
lemma range_ideal [QuasiCompact p] (V : X.affineOpens) :
    LinearMap.range ((ActualClosedIdealModule318.inclusion p).val.app (op V.1)).hom=
      p.ker.ideal V :=
  (range_eq p V.1).trans (ActualClosedIdealModule318.section_kernel_idealData p V)
end ActualClosedIdealRange318
