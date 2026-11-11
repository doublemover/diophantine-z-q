module
public import CocycleLocalFamily318
public section
noncomputable section
namespace CocycleLocalLift318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CocycleLocalCoefficients318 CocycleOverlapCoordinates318 CocycleLocalFamily318
set_option maxHeartbeats 500000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
abbrev restriction (i:ι):X.Modules⥤(U i).toScheme.Modules:=Scheme.Modules.restrictFunctor (U i).ι
@[expose] def localCone (i:ι):Cone ((CocycleModuleCone318.index U c).multicospan⋙restriction U i) where
  pt:=ClutchedModule318.unit (U i).toScheme
  π:={
    app:=fun x=>match x with
      | .left j=>localMap U c i j
      | .right jk=>localMap U c i jk.1≫localLeft U i jk.1 jk.2
    naturality:=by
      intro A B f
      cases f with
      | id A =>
        cases A
        all_goals
          change (𝟙 _)≫_= _≫(restriction U i).map (𝟙 _)
          rw [CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id]
      | fst jk =>
        change (𝟙 _)≫(localMap U c i jk.1≫localLeft U i jk.1 jk.2)=
          localMap U c i jk.1≫localLeft U i jk.1 jk.2
        exact Category.id_comp _
      | snd jk =>
        change (𝟙 _)≫(localMap U c i jk.1≫localLeft U i jk.1 jk.2)=
          localMap U c i jk.2≫localRight U c i jk.1 jk.2
        rw [Category.id_comp]
        exact compatible U c i jk.1 jk.2 }

@[expose] def localLift (i:ι):ClutchedModule318.unit (U i).toScheme⟶
    (CocycleModule318.object U c).restrict (U i).ι:=
  (CocycleModuleCone318.restrictedIsLimit U c (U i).ι).lift (localCone U c i)
lemma localLift_coefficient (i j:ι):
    localLift U c i≫(restriction U i).map (CocycleModule318.coefficient U c j)=localMap U c i j:=
  (CocycleModuleCone318.restrictedIsLimit U c (U i).ι).fac (localCone U c i) (.left j)
lemma restricted_hom_ext (i:ι) {M:(U i).toScheme.Modules}
    (a b:M⟶(CocycleModule318.object U c).restrict (U i).ι)
    (h:∀j,a≫(restriction U i).map (CocycleModule318.coefficient U c j)=
      b≫(restriction U i).map (CocycleModule318.coefficient U c j)):a=b:=by
  apply (CocycleModuleCone318.restrictedIsLimit U c (U i).ι).hom_ext
  rintro (j|jk)
  · exact h j
  · change a≫(restriction U i).map (CocycleModule318.coefficient U c jk.1≫CocycleModule318.left U jk.1 jk.2)=
      b≫(restriction U i).map (CocycleModule318.coefficient U c jk.1≫CocycleModule318.left U jk.1 jk.2)
    rw [Functor.map_comp,←Category.assoc,←Category.assoc,h]
end CocycleLocalLift318
