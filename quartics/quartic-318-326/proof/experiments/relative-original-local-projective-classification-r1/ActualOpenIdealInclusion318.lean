module
public import ActualClosedIdealRange318
public import ModuleBasisKernel318
public section
noncomputable section
namespace ActualOpenIdealInclusion318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z X Y : Scheme.{u}} (p : Z ⟶ X) (j : Y ⟶ X) [IsOpenImmersion j]
local notation "M" => ActualClosedIdealModule318.object p

/-- Restrict the ACTUAL original ideal inclusion, then use the genuine
open-immersion structure-sheaf isomorphism, with its original scalar map. -/
@[expose] def hom : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor j).map (ActualClosedIdealModule318.inclusion p) ≫
    (Scheme.Modules.restrictUnitIso j).hom

lemma formula (V : Y.Opens) (s : Γ(M.restrict j,V)) :
    (hom p j).app V s=(j.appIso V).hom
      ((ActualClosedIdealModule318.inclusion p).app (j ''ᵁ V)
        ((M.restrictAppIso j V).hom s)) := rfl

lemma injective (V : Y.Opens) : Function.Injective ((hom p j).app V) := by
  intro a b h
  rw [formula,formula] at h
  apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso j V).hom).1
  apply ModuleBasisKernel318.inclusion_injective (ActualClosedIdealModule318.structure p) (j ''ᵁ V)
  exact (ConcreteCategory.bijective_of_isIso (j.appIso V).hom).1 h

instance mono : Mono (hom p j) := ⟨by
  intro T a b h
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  apply injective p j V
  exact congrArg (fun k => k.app V s) h⟩
end ActualOpenIdealInclusion318
